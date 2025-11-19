import Hammer.Basic
import Hammer.Premise.Select
import Hammer.Translate.Problem
import Hammer.Translate.Monomorphize
import Hammer.Solver.Backend
import Lean.Elab.Tactic

/-!
# `hammer` tactic

把前面几步串起来：收集候选 → 相关度过滤 → 单态化 → 编码 → 并行调求解器 → 报告收尾。

## 用法

```lean
example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by hammer
example : ... := by hammer (timeout := 30, premises := 256, verbose := true)
example : ... := by hammer (close := false)   -- 只报告，不闭合目标
```

可用选项：`premises`、`timeout`、`instances`、`solvers`（逗号分隔的字符串）、
`verbose`、`mono`、`close`。

## 它闭合目标的方式

成功时 `hammer` 用 `Hammer.trustSMT` 闭合目标。**这不是一个证明。**
逆向翻译（把外部证明重建成 Lean 证明项）是本项目有意留空的那一步；
在补上它之前，任何经 `hammer` 关掉的定理都会在 `#print axioms` 里带着 `Hammer.trustSMT`。
-/

namespace Hammer

open Lean Elab Tactic Meta

/-! ## 配置语法 -/

syntax hammerOpt := ident " := " (num <|> ident <|> str)
syntax (name := hammerTac) "hammer" ("(" hammerOpt,* ")")? : tactic

/-- 不依赖具体的语法树下标，直接把所有 `hammerOpt` 节点捞出来。 -/
private partial def collectOpts (s : Syntax) : Array Syntax :=
  if s.isOfKind ``hammerOpt then #[s]
  else s.getArgs.foldl (init := #[]) fun acc c => acc ++ collectOpts c

private def optValue (o : Syntax) : Syntax :=
  let v := o[2]
  if v.getKind == Syntax.missing.getKind || v.getArgs.size == 1 then
    if v.getArgs.size == 1 then v[0] else v
  else v

private def asBool (s : Syntax) : Option Bool :=
  match s.getId.toString with
  | "true"  => some true
  | "false" => some false
  | _       => none

private def parseConfig (stx : Syntax) : TacticM Hammer.Config := do
  let mut cfg : Hammer.Config := {}
  for o in collectOpts stx do
    let key := o[0].getId.toString
    let v := optValue o
    match key with
    | "premises"  => if let some n := v.isNatLit? then cfg := { cfg with maxPremises := n }
    | "timeout"   => if let some n := v.isNatLit? then cfg := { cfg with timeout := n }
    | "instances" => if let some n := v.isNatLit? then cfg := { cfg with maxInstances := n }
    | "verbose"   => cfg := { cfg with verbose := (asBool v).getD true }
    | "mono"      => cfg := { cfg with monomorphize := (asBool v).getD true }
    | "close"     => cfg := { cfg with closeGoal := (asBool v).getD true }
    | "reconstruct" => cfg := { cfg with reconstruct := (asBool v).getD true }
    | "assumeNonempty" => cfg := { cfg with assumeNonempty := (asBool v).getD true }
    | "solvers"   =>
        if let some s := v.isStrLit? then
          cfg := { cfg with solvers := (s.splitOn ",").map (·.trimAscii.toString) }
    | k => throwErrorAt o "hammer: 未知选项 `{k}`"
  return cfg

/-! ## 主流程 -/

/-- 目标与局部假设一起决定"相关"的符号集。 -/
private def goalSymbols (goalType : Expr) (locals : Array Fact) : Std.HashSet Name :=
  locals.foldl (init := featuresOf goalType) fun acc f =>
    f.symbols.fold (init := acc) fun a n => a.insert n

/-- 一次 `hammer` 调用的全部产出，供报告使用。 -/
structure Outcome where
  attempts  : Array Attempt
  encoded   : Encoded
  path      : System.FilePath
  selected  : Nat
  instances : Nat

/-- 前 4 步：选前提、单态化、编码、调求解器。不碰目标。 -/
def hammerSearch (cfg : Hammer.Config) (g : MVarId) : MetaM Outcome := g.withContext do
  let goalType ← instantiateMVars (← g.getType)
  unless ← isProp goalType do
    throwError "hammer: 目标不是命题"
  let locals ← collectLocalFacts g
  let pool ← collectGlobalFacts
  let selected := selectPremises cfg (goalSymbols goalType locals) pool
  -- 实例化用的具体类型只来自目标与局部上下文。
  let types ← collectGroundTypes (#[goalType] ++ locals.map (·.type))
  let types := types.take 8
  let mut facts := locals
  for f in selected do
    if cfg.monomorphize then
      facts := facts ++ (← monomorphizeFact cfg f types)
    else if !f.isPoly then
      facts := facts.push f
  -- 单态化会放大条数，这里再封一次顶。
  let allFacts := facts.take (cfg.maxPremises * 2)
  let enc ← encodeProblem cfg goalType allFacts
  if cfg.verbose then
    logInfo m!"hammer: SMT-LIB 问题\n{enc.text}"
  let (attempts, path) ← solve cfg enc.text
  return { attempts, encoded := enc, path
           selected := selected.size, instances := allFacts.size - locals.size }

/-- unsat core 里真正用到的前提名。 -/
private def usedPremises (enc : Encoded) (core : Array String) : Array Name :=
  let names := core.filterMap fun lbl => enc.labels[lbl]?
  names.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n

/-- 统计行：前提在各阶段的存活情况。 -/
private def statsLine (o : Outcome) : MessageData :=
  m!"前提 {o.selected} 选中 → {o.instances} 单态化 → {o.encoded.asserted} 已断言\
    （丢弃 {o.encoded.dropped}）"

private def attemptLines (o : Outcome) : MessageData :=
  MessageData.joinSep (o.attempts.toList.map fun a =>
    m!"  {a.backend}: {a.result.describe} ({a.millis}ms)") "\n"

/--
逆向翻译的挂钩。

核心库不硬依赖 Duper：`Hammer.Reconstruct` 被导入时会把 Duper 装进这个 ref，
没导入就是 `none`，`hammer` 退回信任公理。
-/
initialize reconstructHook :
    IO.Ref (Option (Hammer.Config → Array Name → TacticM Bool)) ← IO.mkRef none

/-- 用信任公理闭合目标。 -/
def closeWithTrust (g : MVarId) : MetaM Unit := do
  g.checkNotAssigned `hammer
  let ty ← instantiateMVars (← g.getType)
  g.assign (mkApp (mkConst ``Hammer.trustSMT) ty)

/-- 竞速结果里第一个 `unsat`；没有就报错。 -/
def hammerVerdict (cfg : Hammer.Config) (o : Outcome) : MetaM (Attempt × Array Name) := do
  let some a := o.attempts.find? (fun a => a.result matches .unsat _)
    | throwError m!"hammer: 没有求解器给出 unsat · {statsLine o}\n{attemptLines o}\n\
        可以试试 `hammer (premises := {cfg.maxPremises * 2}, timeout := {cfg.timeout * 3})`；\
        若丢弃数很高，说明目标里有编码器处理不了的构造。"
  let core := match a.result with | .unsat c => c | _ => #[]
  return (a, usedPremises o.encoded core)

@[tactic hammerTac]
def evalHammer : Tactic := fun stx => do
  let cfg ← parseConfig stx
  let g ← getMainGoal
  let o ← hammerSearch cfg g
  let (a, used) ← hammerVerdict cfg o
  let usedMsg :=
    if used.isEmpty then m!"求解器没有返回 unsat core"
    else MessageData.joinSep (used.toList.map fun n => m!"  · {n}") "\n"
  let detail :=
    if cfg.verbose then m!"\n{attemptLines o}\n  问题文件：{o.path}" else m!""
  let header := m!"hammer: {a.backend} 判定 unsat（{a.millis}ms）· {statsLine o}\n\
    unsat core 用到的前提：\n{usedMsg}"
  -- 逆向翻译：拿 core 里的引理让 Duper 在 Lean 内部重证。
  let reconstructed ←
    if cfg.reconstruct then
      match ← reconstructHook.get with
      | some hook => hook cfg used
      | none => pure false
    else pure false
  if reconstructed then
    -- Duper 已经把目标关掉了，而且关得是真的。
    logInfo m!"{header}\n目标已由 Duper 重建的证明项闭合 —— 这是真证明，不含 `trustSMT`。{detail}"
  else
    let why := if cfg.reconstruct then "（Duper 重建失败或未启用）" else ""
    logInfo m!"{header}\n目标已由 `Hammer.trustSMT` 闭合 —— 这不是证明{why}。{detail}"
    if cfg.closeGoal then
      closeWithTrust g
      replaceMainGoal []
    else
      replaceMainGoal [g]

end Hammer
