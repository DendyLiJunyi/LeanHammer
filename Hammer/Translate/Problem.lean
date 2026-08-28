import Hammer.Translate.Encode

/-!
# Assembling the full SMT-LIB problem

The goal is translated first -- if that fails, the whole call fails. Premises follow one
by one; a premise that cannot be translated is simply dropped. Every assert carries a
`:named` label so the solver's unsat core can be mapped back to Lean lemma names.
-/

namespace Hammer

open Lean Meta

/-- A translated problem, ready to hand to a solver. -/
structure Encoded where
  /-- The SMT-LIB 2 text. -/
  text     : String
  /-- Assert label to premise name. -/
  labels   : Std.HashMap String Name
  /-- How many premises were translated and asserted. -/
  asserted : Nat
  /-- How many premises were dropped as unencodable. -/
  dropped  : Nat

/-- Run the encoder. -/
def EncM.run' (cfg : Hammer.Config) (x : EncM α) : MetaM (α × EncState) := do
  (x.run { cfg }).run {}

/--
Encode the goal and its premises into SMT-LIB. The resulting problem asserts
**premises ∧ ¬goal**, so `unsat` from the solver means exactly "the premises entail the
goal".
-/
def encodeProblem (cfg : Hammer.Config) (goalType : Expr) (facts : Array Fact) :
    MetaM Encoded := do
  let go : EncM (Sexp × Array (String × Name) × Array Command × Nat) := do
    -- Translate the goal first: it fixes which sorts and symbols exist, and it
    -- surfaces a failure immediately.
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
          -- A premise that translates to `true` carries no information and only slows
          -- the solver down.
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
      ++ (if sideAsserts.isEmpty then #[] else #[Command.raw "; Nat non-negativity"])
      ++ sideAsserts
      ++ asserts
      ++ #[Command.raw "; negated goal", Command.assert (some "goal") negGoal]
  let problem : Problem := { produceCores := cfg.unsatCores, commands := commands }
  return {
    text := problem.render
    labels := Std.HashMap.ofList labels.toList
    asserted := labels.size
    dropped := dropped }

end Hammer
