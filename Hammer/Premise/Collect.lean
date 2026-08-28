import Hammer.Premise.Features

/-!
# Collecting candidate premises

Two sources: the goal's local context, and the whole `Environment`. The latter means
scanning hundreds of thousands of constants, so it is cached in-process and keyed on the
environment's size.

Only `theorem`s are collected. A theorem's type is necessarily a proposition, which lets
the whole scan stay pure -- no `isProp` call per constant, which would add seconds to
every `hammer` invocation.
-/

namespace Hammer

open Lean Meta

/-- Cache for the global candidate pool: `(constant count, pool)`. Invalidated
automatically as the environment grows. -/
initialize globalFactCache : IO.Ref (Option (Nat × Array Fact)) ← IO.mkRef none

/-- Whether the statement still binds type or universe variables, which decides whether
monomorphization is needed. -/
private def hasSortBinder : Expr → Bool
  | .forallE _ d b _ => d.isSort || hasSortBinder b
  | _ => false

private def statementIsPolymorphic (ci : ConstantInfo) : Bool :=
  !ci.levelParams.isEmpty || hasSortBinder ci.type

/-- Scan the environment and build the global candidate pool. -/
def collectGlobalFacts : MetaM (Array Fact) := do
  let env ← getEnv
  -- `map₂` holds the constants added by the current file; it is normally tiny, so
  -- counting it is cheap.
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

/-- Take every propositional hypothesis from the goal's local context. -/
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
