import Hammer.Translate.Encode
import Hammer.Premise.Features

/-!
# 单态化

Mathlib 的引理几乎全是多态的：`∀ {α : Type u} [inst : Monoid α], …`。一阶编码器碰到
`∀ (α : Type u)` 只能放弃，所以必须先把类型变量替换成目标里真实出现的具体类型，
再用 `synthInstance` 补齐类型类参数。

策略是"目标驱动"的：候选类型只来自目标与局部上下文。这正是 hammer 在实践中管用的
原因——不需要枚举整个类型宇宙，用户想证的东西已经把类型说清楚了。
-/

namespace Hammer

open Lean Meta

/-- `a` 是否是一个适合拿来实例化类型变量的具体类型。 -/
private def isTypeCandidate (a : Expr) : MetaM Bool := do
  if a.hasExprMVar || a.hasLooseBVars then return false
  if a.isSort || a.isForall then return false
  let t ← whnfR (← inferType a)
  unless t.isSort do return false
  -- `Prop` 不作为实例化目标：编码器把命题当 `Bool`，实例化到 `Prop` 收益很小。
  if t matches .sort .zero then return false
  if (← isClass? a).isSome then return false
  return true

private abbrev GatherM := StateRefT (Std.HashSet ExprStructEq × Array Expr) MetaM

private def record (a : Expr) : GatherM Unit := do
  let key : ExprStructEq := a
  let (seen, out) ← get
  unless seen.contains key do
    set (seen.insert key, out.push a)

private partial def gather (e : Expr) : GatherM Unit := do
  match e with
  | .app .. =>
      for a in e.getAppArgs do
        if !a.hasLooseBVars then
          if ← isTypeCandidate a then record a
        gather a
      gather e.getAppFn
  | .lam _ d b _ | .forallE _ d b _ => gather d; gather b
  | .letE _ t v b _ => gather t; gather v; gather b
  | .mdata _ b => gather b
  | .proj _ _ b => gather b
  | _ => pure ()

/-- 从目标与局部假设里收集实例化用的具体类型。 -/
def collectGroundTypes (es : Array Expr) : MetaM (Array Expr) := do
  let go : GatherM Unit := do
    for e in es do
      gather e
      -- 表达式本身也可能就是一个类型。
      if !e.hasLooseBVars then
        if ← isTypeCandidate e then record e
  let (_, (_, types)) ← go.run (∅, #[])
  return types

/-- 剥掉前导的类型绑定与实例绑定，换成元变量。 -/
private partial def peelBinders (e ty : Expr) (tms : Array Expr) (ims : Array MVarId) :
    MetaM (Expr × Expr × Array Expr × Array MVarId) := do
  let ty ← if ty.isForall then pure ty else whnfR ty
  match ty with
  | .forallE _ d b bi =>
      if (← whnfR d).isSort then
        let m ← mkFreshExprMVar d
        peelBinders (mkApp e m) (b.instantiate1 m) (tms.push m) ims
      else if bi.isInstImplicit then
        let m ← mkFreshExprMVar d
        peelBinders (mkApp e m) (b.instantiate1 m) tms (ims.push m.mvarId!)
      else
        return (e, ty, tms, ims)
  | _ => return (e, ty, tms, ims)

/-- 把类型变量赋成 `assign` 的一次尝试；实例参数交给类型类合成。 -/
private def tryInstantiate (f : Fact) (ci : ConstantInfo) (assign : Array Expr) :
    MetaM (Option Fact) := withoutModifyingState do
  let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let base := mkConst f.name lvls
  let ty := ci.instantiateTypeLevelParams lvls
  let (e, resTy, tms, ims) ← peelBinders base ty #[] #[]
  if tms.size != assign.size then return none
  for (m, t) in tms.zip assign do
    unless ← isDefEq m t do return none
  for im in ims do
    let itype ← instantiateMVars (← im.getType)
    if itype.hasExprMVar then return none
    match ← trySynthInstance itype with
    | .some inst => unless ← isDefEq (mkMVar im) inst do return none
    | _ => return none
  let resTy ← instantiateMVars resTy
  if resTy.hasExprMVar || resTy.hasLevelMVar then return none
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasLevelMVar then return none
  return some { f with
    type := resTy, proof := e, symbols := featuresOf resTy, isPoly := false }

/-- `types` 上长度为 `k` 的全部组合，总数封顶 `cap`。 -/
private def tuples (types : Array Expr) (k : Nat) (cap : Nat) : Array (Array Expr) := Id.run do
  let mut acc : Array (Array Expr) := #[#[]]
  for _ in [0:k] do
    let mut next : Array (Array Expr) := #[]
    for t in acc do
      for ty in types do
        if next.size < cap then next := next.push (t.push ty)
    acc := next
  return acc

/-- 把一条（可能多态的）引理实例化成若干条单态引理。 -/
def monomorphizeFact (cfg : Hammer.Config) (f : Fact) (types : Array Expr) :
    MetaM (Array Fact) := do
  if f.isLocal || !f.isPoly then return #[f]
  let some ci := (← getEnv).find? f.name | return #[]
  -- 先数一下要填几个类型变量。
  let k ← withoutModifyingState do
    let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let (_, _, tms, _) ← peelBinders (mkConst f.name lvls) (ci.instantiateTypeLevelParams lvls) #[] #[]
    return tms.size
  -- 类型变量太多就放弃：组合爆炸，且这类引理通常也不是目标要的。
  if k > 2 then return #[]
  let mut out : Array Fact := #[]
  let mut seen : Std.HashSet ExprStructEq := ∅
  for assign in tuples types k cfg.maxInstances do
    if out.size ≥ cfg.maxInstances then break
    if let some g ← tryInstantiate f ci assign then
      let key : ExprStructEq := g.type
      unless seen.contains key do
        seen := seen.insert key
        out := out.push g
  return out

end Hammer
