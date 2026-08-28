import Hammer.Basic
import Hammer.Premise.Select
import Hammer.Translate.Problem
import Hammer.Translate.Monomorphize
import Hammer.Solver.Backend
import Lean.Elab.Tactic

/-!
# The `hammer` tactic

Ties the pipeline together: collect candidates, filter by relevance, monomorphize, encode,
race the solvers, report.

## Usage

```lean
example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by hammer
example : ... := by hammer (timeout := 30, premises := 256, verbose := true)
example : ... := by hammer (close := false)   -- report only, leave the goal open
```

Available options: `premises`, `timeout`, `instances`, `solvers` (a comma-separated
string), `verbose`, `mono`, `close`, `reconstruct`, `assumeNonempty`.

## How the goal gets closed

With `Hammer.Reconstruct` imported, `hammer` first hands the unsat core to Duper to be
reproved inside Lean. When that works the goal is closed by a genuine proof term.
Otherwise it falls back to the `Hammer.trustSMT` axiom, which is **not a proof** -- such
theorems show `Hammer.trustSMT` under `#print axioms`, and the report says so explicitly.
-/

namespace Hammer

open Lean Elab Tactic Meta

/-! ## Option syntax -/

syntax hammerOpt := ident " := " (num <|> ident <|> str)
syntax (name := hammerTac) "hammer" ("(" hammerOpt,* ")")? : tactic

/-- Grab every `hammerOpt` node without depending on syntax-tree indices. -/
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
    | k => throwErrorAt o "hammer: unknown option `{k}`"
  return cfg

/-! ## Main pipeline -/

/-- The goal together with its local hypotheses fixes the initial relevant-symbol set. -/
private def goalSymbols (goalType : Expr) (locals : Array Fact) : Std.HashSet Name :=
  locals.foldl (init := featuresOf goalType) fun acc f =>
    f.symbols.fold (init := acc) fun a n => a.insert n

/-- Everything one `hammer` call produced, for reporting. -/
structure Outcome where
  attempts  : Array Attempt
  encoded   : Encoded
  path      : System.FilePath
  selected  : Nat
  instances : Nat

/-- The search half: select premises, monomorphize, encode, call the solvers. Does not
touch the goal. -/
def hammerSearch (cfg : Hammer.Config) (g : MVarId) : MetaM Outcome := g.withContext do
  let goalType ← instantiateMVars (← g.getType)
  unless ← isProp goalType do
    throwError "hammer: the goal is not a proposition"
  let locals ← collectLocalFacts g
  let pool ← collectGlobalFacts
  let selected := selectPremises cfg (goalSymbols goalType locals) pool
  -- Instantiation types come only from the goal and the local context.
  let types ← collectGroundTypes (#[goalType] ++ locals.map (·.type))
  let types := types.take 8
  let mut facts := locals
  for f in selected do
    if cfg.monomorphize then
      facts := facts ++ (← monomorphizeFact cfg f types)
    else if !f.isPoly then
      facts := facts.push f
  -- Monomorphization multiplies the count, so cap it once more.
  let allFacts := facts.take (cfg.maxPremises * 2)
  let enc ← encodeProblem cfg goalType allFacts
  if cfg.verbose then
    logInfo m!"hammer: SMT-LIB problem\n{enc.text}"
  let (attempts, path) ← solve cfg enc.text
  return { attempts, encoded := enc, path
           selected := selected.size, instances := allFacts.size - locals.size }

/-- The premise names that actually appear in the unsat core. -/
private def usedPremises (enc : Encoded) (core : Array String) : Array Name :=
  let names := core.filterMap fun lbl => enc.labels[lbl]?
  names.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n

/-- Stats line: how many premises survived each stage. -/
private def statsLine (o : Outcome) : MessageData :=
  m!"premises: {o.selected} selected → {o.instances} monomorphized → \
    {o.encoded.asserted} asserted ({o.encoded.dropped} dropped)"

private def attemptLines (o : Outcome) : MessageData :=
  MessageData.joinSep (o.attempts.toList.map fun a =>
    m!"  {a.backend}: {a.result.describe} ({a.millis}ms)") "\n"

/--
The proof-reconstruction hook.

The core library does not depend on Duper: importing `Hammer.Reconstruct` installs Duper
into this ref. Left as `none`, `hammer` falls back to the trust axiom.
-/
initialize reconstructHook :
    IO.Ref (Option (Hammer.Config → Array Name → TacticM Bool)) ← IO.mkRef none

/-- Close the goal with the trust axiom. -/
def closeWithTrust (g : MVarId) : MetaM Unit := do
  g.checkNotAssigned `hammer
  let ty ← instantiateMVars (← g.getType)
  g.assign (mkApp (mkConst ``Hammer.trustSMT) ty)

/-- The first `unsat` among the racing solvers, or an error if there is none. -/
def hammerVerdict (cfg : Hammer.Config) (o : Outcome) : MetaM (Attempt × Array Name) := do
  let some a := o.attempts.find? (fun a => a.result matches .unsat _)
    | throwError m!"hammer: no solver returned unsat · {statsLine o}\n{attemptLines o}\n\
        Try `hammer (premises := {cfg.maxPremises * 2}, timeout := {cfg.timeout * 3})`. \
        A high drop count means the goal contains constructs the encoder cannot handle."
  let core := match a.result with | .unsat c => c | _ => #[]
  return (a, usedPremises o.encoded core)

@[tactic hammerTac]
def evalHammer : Tactic := fun stx => do
  let cfg ← parseConfig stx
  let g ← getMainGoal
  let o ← hammerSearch cfg g
  let (a, used) ← hammerVerdict cfg o
  let usedMsg :=
    if used.isEmpty then m!"  (the solver returned no usable unsat core)"
    else MessageData.joinSep (used.toList.map fun n => m!"  · {n}") "\n"
  let detail :=
    if cfg.verbose then m!"\n{attemptLines o}\n  problem file: {o.path}" else m!""
  let header := m!"hammer: {a.backend} returned unsat ({a.millis}ms) · {statsLine o}\n\
    premises in the unsat core:\n{usedMsg}"
  -- Proof reconstruction: hand the core's lemmas to Duper to reprove inside Lean.
  let reconstructed ←
    if cfg.reconstruct then
      match ← reconstructHook.get with
      | some hook => hook cfg used
      | none => pure false
    else pure false
  if reconstructed then
    -- Duper already closed the goal, and closed it for real.
    logInfo m!"{header}\ngoal closed by a proof term reconstructed with Duper — a real proof, \
      no `trustSMT`.{detail}"
  else
    let why := if cfg.reconstruct then " (Duper reconstruction failed or is unavailable)" else ""
    logInfo m!"{header}\ngoal closed by `Hammer.trustSMT` — this is not a proof{why}.{detail}"
    if cfg.closeGoal then
      closeWithTrust g
      replaceMainGoal []
    else
      replaceMainGoal [g]

end Hammer
