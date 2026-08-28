import Hammer.Translate.Encode

/-!
# 组装完整的 SMT-LIB 问题

先翻目标（失败就整体失败），再逐条翻前提（失败就丢掉那一条）。
断言带 `:named` 标签，这样求解器返回的 unsat core 能反查回 Lean 的引理名。
-/

namespace Hammer

open Lean Meta

/-- 一个已经翻好、可以直接喂给求解器的问题。 -/
structure Encoded where
  /-- SMT-LIB 2 文本。 -/
  text     : String
  /-- 断言标签 → 前提名。 -/
  labels   : Std.HashMap String Name
  /-- 成功翻译并断言的前提数。 -/
  asserted : Nat
  /-- 因不可编码而丢弃的前提数。 -/
  dropped  : Nat

/-- 跑一次编码器。 -/
def EncM.run' (cfg : Hammer.Config) (x : EncM α) : MetaM (α × EncState) := do
  (x.run { cfg }).run {}

/--
把目标与前提编码成 SMT-LIB。返回的问题断言的是 **前提 ∧ ¬目标**，
所以求解器给出 `unsat` 就等于"前提蕴含目标"。
-/
def encodeProblem (cfg : Hammer.Config) (goalType : Expr) (facts : Array Fact) :
    MetaM Encoded := do
  let go : EncM (Sexp × Array (String × Name) × Array Command × Nat) := do
    -- 目标先翻：它决定了哪些排序/符号存在，也让报错第一时间暴露。
    let negGoal := Sexp.not' (← encodeForm goalType)
    let mut asserts : Array Command := #[]
    let mut labels : Array (String × Name) := #[]
    let mut dropped := 0
    for (f, i) in facts.zipIdx do
      let r? : Option Sexp ←
        try pure (some (← encodeForm f.type))
        catch _ => pure none
      match r? with
      | some s =>
          -- 翻成恒真的前提没有信息量，只会拖慢求解器。
          if s == Sexp.true' then
            dropped := dropped + 1
          else
            let lbl := s!"p{i}"
            asserts := asserts.push (.raw s!"; {lbl} : {f.name}")
            asserts := asserts.push (.assert (some lbl) s)
            labels := labels.push (lbl, f.name)
      | none => dropped := dropped + 1
    return (negGoal, labels, asserts, dropped)
  let ((negGoal, labels, asserts, dropped), st) ← EncM.run' cfg go
  let sideAsserts := st.sideAx.map fun a => Command.assert none a
  let commands :=
    st.decls
      ++ (if sideAsserts.isEmpty then #[] else #[Command.raw "; Nat 非负性"])
      ++ sideAsserts
      ++ asserts
      ++ #[Command.raw "; 取反后的目标", Command.assert (some "goal") negGoal]
  let problem : Problem := { produceCores := cfg.unsatCores, commands := commands }
  return {
    text := problem.render
    labels := Std.HashMap.ofList labels.toList
    asserted := labels.size
    dropped := dropped }

end Hammer
