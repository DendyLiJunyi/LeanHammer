import Hammer.Premise.Features

/-!
# 候选前提的收集

两个来源：当前目标的局部上下文，和整个 `Environment`。后者要扫十万量级的常量，
所以按 environment 大小做了一层进程内缓存。

只收 `theorem`：定理的类型必然是命题，于是整趟扫描可以纯函数完成，不必对每个常量
调 `isProp`（那会让一次 `hammer` 多花好几秒）。
-/

namespace Hammer

open Lean Meta

/-- 全局候选池的缓存：`(常量数, 候选池)`。environment 增长时自动失效。 -/
initialize globalFactCache : IO.Ref (Option (Nat × Array Fact)) ← IO.mkRef none

/-- 陈述里是否还留着类型/宇宙层面的变量（决定要不要走单态化）。 -/
private def hasSortBinder : Expr → Bool
  | .forallE _ d b _ => d.isSort || hasSortBinder b
  | _ => false

private def statementIsPolymorphic (ci : ConstantInfo) : Bool :=
  !ci.levelParams.isEmpty || hasSortBinder ci.type

/-- 扫描 environment，建立全局候选池。 -/
def collectGlobalFacts : MetaM (Array Fact) := do
  let env ← getEnv
  -- `map₂` 是当前文件新增的常量，通常很小，数一遍不贵。
  let size := env.constants.map₁.size + env.constants.map₂.foldl (fun n _ _ => n + 1) 0
  if let some (cachedSize, facts) ← globalFactCache.get then
    if cachedSize == size then return facts
  let facts : Array Fact := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo _ =>
        if isBlacklisted n || isNoise n then acc
        else acc.push {
          name := n
          type := ci.type
          proof := mkConst n (ci.levelParams.map mkLevelParam)
          symbols := featuresOf ci.type
          isLocal := false
          isPoly := statementIsPolymorphic ci }
    | _ => acc
  globalFactCache.set (some (size, facts))
  return facts

/-- 从目标的局部上下文里取出所有命题假设。 -/
def collectLocalFacts (g : MVarId) : MetaM (Array Fact) := g.withContext do
  let mut out : Array Fact := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless (← isProp ty) do continue
    out := out.push {
      name := d.userName
      type := ty
      proof := d.toExpr
      symbols := featuresOf ty
      isLocal := true }
  return out

end Hammer
