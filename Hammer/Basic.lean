import Lean

/-!
# Core types and configuration

Configuration, result types, and the trust axiom used when proof reconstruction is
unavailable or fails. Everything here is shared across the whole pipeline.
-/

namespace Hammer

open Lean

/-- Description of an external SMT solver backend. -/
structure Backend where
  /-- Name used in reports and in the `solvers` option, e.g. `"z3"`. -/
  name    : String
  /-- Executable name, looked up on `PATH`. -/
  exe     : String
  /-- Build the command line, given a timeout in seconds and the problem file. -/
  args    : Nat → System.FilePath → Array String
  deriving Inhabited

/-- Configuration for `hammer`. -/
structure Config where
  /-- Maximum number of lemmas handed to the solver after relevance filtering. -/
  maxPremises  : Nat := 96
  /-- Wall-clock timeout per solver, in seconds. -/
  timeout      : Nat := 10
  /-- Names of the backends to race in parallel. -/
  solvers      : List String := ["z3", "cvc5"]
  /-- Print the SMT-LIB problem and the raw solver output. -/
  verbose      : Bool := false
  /-- Request an unsat core, so the report can name the premises actually used. -/
  unsatCores   : Bool := true
  /-- Instantiate polymorphic lemmas at concrete types. -/
  monomorphize : Bool := true
  /-- Maximum number of instances generated per lemma during monomorphization. -/
  maxInstances : Nat := 8
  /-- When `false`, report but leave the goal open. -/
  closeGoal    : Bool := true
  /--
  After an unsat core comes back, try to reprove the goal inside Lean with Duper.

  On success the goal is closed by a genuine proof term and `trustSMT` never appears;
  on failure we fall back to the trust axiom. This is proof reconstruction, outsourced:
  the external solver does the search, Duper does the rebuilding.
  Only takes effect once `Hammer.Reconstruct` is imported.
  -/
  reconstruct  : Bool := true
  /-- Heartbeat budget for a single Duper reconstruction attempt. -/
  reconstructHeartbeats : Nat := 400000
  /--
  Allow declaring an uninterpreted sort for a Lean type that cannot be shown nonempty.

  SMT-LIB assumes every sort is nonempty, whereas Lean types can be empty:
  `∀ x : Empty, P x` holds vacuously in Lean but becomes a real assertion in SMT.
  The default (`false`) requires a synthesizable `Nonempty` instance and would rather
  drop a premise than risk it. Setting `true` buys coverage at the cost of trusting
  `unsat`.
  -/
  assumeNonempty : Bool := false
  deriving Inhabited, Repr

/-- A solver's answer to one problem. -/
inductive SolverResult where
  /-- Unsatisfiable, i.e. the goal follows. `core` holds the names of the asserts in the
  unsat core. -/
  | unsat (core : Array String)
  /-- Satisfiable: under this encoding, the goal does not follow. -/
  | sat
  /-- Timeout, out of memory, or the solver gave up. -/
  | unknown (reason : String)
  /-- Invoking the solver itself failed (not installed, crashed, ...). -/
  | error (msg : String)
  deriving Inhabited, Repr

/--
The trust axiom. `hammer` closes the goal with it once an external SMT solver reports
that the selected premises together with the negated goal are unsatisfiable.

**This is not a proof.** The axiom makes `p` hold unconditionally, so any theorem closed
through it shows `Hammer.trustSMT` under `#print axioms`.

We only reach it when proof reconstruction fails. With `Hammer.Reconstruct` imported,
`hammer` first hands the unsat core to Duper to be reproved inside Lean; when that
succeeds the goal is closed by a real proof term and this axiom never appears. Duper has
no arithmetic decision procedure, so purely arithmetic goals still land here.
-/
axiom trustSMT (p : Prop) : p

end Hammer
