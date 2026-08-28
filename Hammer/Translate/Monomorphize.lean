import Hammer.Translate.Encode
import Hammer.Premise.Features

/-!
# Monomorphization

Mathlib lemmas are almost all polymorphic: `∀ {α : Type u} [inst : Monoid α], …`. A
first-order encoder has no choice but to give up on `∀ (α : Type u)`, so type variables
must first be replaced by concrete types that actually occur in the goal, with type class
arguments filled in by `synthInstance`.

The strategy is goal-driven: candidate types come only from the goal and the local
context. This is precisely why hammers work in practice -- there is no need to enumerate
the universe of types, because what the user is trying to prove already pins them down.
-/

namespace Hammer

open Lean Meta

/-- Whether `a` is a concrete type suitable for instantiating a type variable. -/
private def isTypeCandidate (a : Expr) : MetaM Bool := do
  if a.hasExprMVar || a.hasLooseBVars then return false
  if a.isSort || a.isForall then return false
  let t ← whnfR (← inferType a)
  unless t.isSort do return false
  -- `Prop` is not an instantiation target: the encoder already treats propositions as
  -- `Bool`, so instantiating at `Prop` buys very little.
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

/-- Collect the concrete types to instantiate with, from the goal and its hypotheses. -/
def collectGroundTypes (es : Array Expr) : MetaM (Array Expr) := do
  let go : GatherM Unit := do
    for e in es do
      gather e
      -- The expression itself may be a type.
      if !e.hasLooseBVars then
        if ← isTypeCandidate e then record e
  let (_, (_, types)) ← go.run (∅, #[])
  return types

/-- Peel off leading type and instance binders, replacing them with metavariables. -/
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

/-- One attempt at assigning the type variables from `assign`; instance arguments are
left to type class synthesis. -/
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

/-- All length-`k` tuples over `types`, capped at `cap` in total. -/
private def tuples (types : Array Expr) (k : Nat) (cap : Nat) : Array (Array Expr) := Id.run do
  let mut acc : Array (Array Expr) := #[#[]]
  for _ in [0:k] do
    let mut next : Array (Array Expr) := #[]
    for t in acc do
      for ty in types do
        if next.size < cap then next := next.push (t.push ty)
    acc := next
  return acc

/-- Instantiate one possibly-polymorphic lemma into a set of monomorphic ones. -/
def monomorphizeFact (cfg : Hammer.Config) (f : Fact) (types : Array Expr) :
    MetaM (Array Fact) := do
  if f.isLocal || !f.isPoly then return #[f]
  let some ci := (← getEnv).find? f.name | return #[]
  -- First count how many type variables need filling.
  let k ← withoutModifyingState do
    let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let (_, _, tms, _) ← peelBinders (mkConst f.name lvls) (ci.instantiateTypeLevelParams lvls) #[] #[]
    return tms.size
  -- Too many type variables: the combinatorics blow up, and such lemmas are rarely
  -- what the goal needs anyway.
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
