import Hammer.Basic
import Hammer.Translate.SMTLib

/-!
# Invoking external solvers and parsing their answers

Write the SMT-LIB text to a temporary file, run every configured backend in parallel, and
take the first one that answers `unsat`. Timeouts are enforced by the solvers' own options,
so even when we return early any straggler process kills itself once its timeout hits.
-/

namespace Hammer

open Lean

/-- The built-in backend table. `hammer`'s `solvers` option looks names up here. -/
def knownBackends : Array Backend := #[
  { name := "z3"
    exe  := "z3"
    args := fun t f => #["-smt2", s!"-T:{t}", f.toString] },
  { name := "cvc5"
    exe  := "cvc5"
    args := fun t f => #["--lang=smt2", s!"--tlimit={t * 1000}",
                         "--produce-unsat-cores", f.toString] }
]

def backendByName? (n : String) : Option Backend :=
  knownBackends.find? (·.name == n)

/-- Build a unique `.smt2` path under the system temporary directory. -/
private def freshProblemPath : IO System.FilePath := do
  let base : System.FilePath :=
    match (← IO.getEnv "TMPDIR") with
    | some d => d
    | none   => "/tmp"
  let dir := base / "lean-hammer"
  IO.FS.createDirAll dir
  let stamp ← IO.monoNanosNow
  let salt ← IO.rand 0 999999
  return dir / s!"q-{stamp}-{salt}.smt2"

/-- Pull the unsat core labels out of the solver's output. -/
private def parseCore (rest : List String) : Array String := Id.run do
  let text := String.intercalate " " rest
  let mut out : Array String := #[]
  let mut cur : String := ""
  for c in text.toList do
    if c.isAlphanum || c == '_' || c == '!' then
      cur := cur.push c
    else
      if !cur.isEmpty then out := out.push cur
      cur := ""
  if !cur.isEmpty then out := out.push cur
  return out

/-- Parse the standard output of z3 / cvc5. -/
def parseOutput (stdout stderr : String) (exitCode : UInt32) : SolverResult := Id.run do
  let lines := (stdout.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  let mut idx := 0
  for l in lines do
    if l == "unsat" then
      return .unsat (parseCore (lines.drop (idx + 1)))
    if l == "sat" then
      return .sat
    if l == "unknown" || l.startsWith "timeout" then
      return .unknown l
    idx := idx + 1
  if exitCode != 0 || !stderr.isEmpty then
    return .error (if stderr.isEmpty then s!"exit code {exitCode}" else stderr.trimAscii.toString)
  return .unknown "solver reported neither sat, unsat, nor unknown"

/-- A readable summary of a result, for the report. -/
def SolverResult.describe : SolverResult → String
  | .unsat core => s!"unsat (core size {core.size})"
  | .sat => "sat"
  | .unknown r => s!"unknown: {r}"
  | .error m => s!"error: {m}"

/-- Run a single backend. Any exception collapses into `.error`. -/
def runBackend (b : Backend) (timeout : Nat) (path : System.FilePath) :
    BaseIO SolverResult := do
  let act : IO SolverResult := do
    let out ← IO.Process.output { cmd := b.exe, args := b.args timeout path }
    return parseOutput out.stdout out.stderr out.exitCode
  match ← act.toBaseIO with
  | .ok r => return r
  | .error e => return .error s!"could not run {b.exe}: {e}"

/-- The full record of one solving attempt, for reporting. -/
structure Attempt where
  backend : String
  result  : SolverResult
  millis  : Nat

/--
Race the problem across every backend in parallel. Returns all attempt records; once the
first `unsat` arrives we stop waiting on the rest. `problemText` is written to a temporary
file whose path is returned too, so `verbose` can point at it.
-/
def solve (cfg : Config) (problemText : String) :
    IO (Array Attempt × System.FilePath) := do
  let path ← freshProblemPath
  IO.FS.writeFile path problemText
  let backends := cfg.solvers.filterMap backendByName? |>.toArray
  if backends.isEmpty then
    return (#[⟨"<none>", .error "no usable backend; check the solvers option", 0⟩], path)
  let start ← IO.monoMsNow
  let tasks ← backends.mapM fun b =>
    return (b.name, ← BaseIO.asTask (runBackend b cfg.timeout path))
  -- Poll: return as soon as anyone reports unsat.
  let mut done : Array Attempt := #[]
  let mut pending := tasks
  while !pending.isEmpty do
    let mut stillPending : Array (String × Task SolverResult) := #[]
    for (name, t) in pending do
      if (← IO.getTaskState t) == .finished then
        let r := t.get
        done := done.push ⟨name, r, (← IO.monoMsNow) - start⟩
        if let .unsat _ := r then
          return (done, path)
      else
        stillPending := stillPending.push (name, t)
    pending := stillPending
    if !pending.isEmpty then
      IO.sleep 15
  return (done, path)

end Hammer
