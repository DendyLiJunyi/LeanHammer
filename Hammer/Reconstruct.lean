import Hammer.Tactic
import Duper.Tactic

/-!
# Proof reconstruction, outsourced to Duper

An unsat core from an external SMT solver says "these few premises suffice", but it gives
Lean nothing checkable. Duper is a superposition prover that runs inside Lean and emits
genuine proof terms, so the cheapest reconstruction available is: **hand the core's lemmas
to Duper and let it reprove the goal inside Lean**.

That division of labour is the classic hammer shape. The external solver does the
*search* across tens of thousands of lemmas; Duper does the *rebuilding* over the handful
that survive. Once the core has cut the search space down to single digits, Duper is
usually enough.

## The coverage gap

Duper is pure first-order equational reasoning with **no arithmetic decision procedure**.
For goals decided by z3's linear arithmetic (`a ≤ b → a ≤ b + 1`, `n - (n+1) = 0`), the
core often contains just one or two hypotheses and all the real work sits in the solver's
arithmetic theory -- which Duper cannot pick up. What transfers cleanly are goals that are
genuinely equational or first-order.

Importing this module enables reconstruction; `hammer (reconstruct := false)` turns it
off.
-/

namespace Hammer

open Lean Elab Tactic Meta

/-- Call Duper with the lemmas from the unsat core. `*` lets Duper gather the local
context itself. -/
def duperReconstruct (cfg : Hammer.Config) (used : Array Name) : TacticM Bool := do
  let env ← getEnv
  -- `*` brings in the local hypotheses, so we only add global lemmas here. `mkCIdent`
  -- pre-resolves the name, sidestepping namespaces and shadowing.
  let idents : Array Term := used.filterMap fun n =>
    if env.contains n then some ⟨mkCIdent n⟩ else none
  let stx ← if idents.isEmpty then
      `(tactic| duper [*] [] {})
    else
      `(tactic| duper [*, $idents,*] [] {})
  let s ← saveState
  try
    withOptions (fun o => o.set `maxHeartbeats cfg.reconstructHeartbeats) do
      Core.withCurrHeartbeats do
        evalTactic stx
    -- Duper is a terminal tactic: if it ran, the goal is closed.
    return true
  catch _ =>
    s.restore
    return false

initialize reconstructHook.set (some duperReconstruct)

end Hammer
