import Hammer

/-!
# Chronological library-reproving benchmark

The standard hammer evaluation (Sledgehammer's "Judgment Day", the LeanHammer / lean-auto
Mathlib evaluations): take existing library theorems, and try to reprove each one using
**only premises declared strictly before it**. Modules are stored in the environment in
import (topological) order and `ModuleData.constNames` is in declaration order, so the
pair (module index, position) is a linear order in which nothing can depend on anything
after it. This excludes the theorem itself and everything derived from it.

Targets: `theorem`s from core Lean's `Init.Data.Nat`, `Init.Data.Int`, `Init.Data.List`
modules, minus compiler/elaborator noise, sampled deterministically by name hash.

Each target is turned into a goal (universe parameters instantiated at `1`), `intros`
applied, and run through the same pipeline as `hammer` with the default `Config`.
Recorded per target:
* `solved`        -- some solver returned `unsat`
* `reconstructed` -- Duper closed the goal from the core, and the resulting term
  passes the kernel (`addDecl`) with no `trustSMT` / `sorryAx`

Environment variables: `BENCH_N` (sample size, default 200), `BENCH_SHARD`,
`BENCH_SHARDS` (for parallel runs), `BENCH_OUT` (TSV path), `BENCH_TIMEOUT` (seconds per
solver, default = `Config` default).

Run: `lake env lean HammerBench/Chrono.lean`
-/

open Lean Meta Elab Tactic Hammer

namespace HammerBench

def targetModulePrefixes : List Name :=
  [`Init.Data.Nat, `Init.Data.Int, `Init.Data.List]

/-- Global declaration position: (module index, index within the module). -/
def positionMap (env : Environment) : Std.HashMap Name Nat := Id.run do
  let mut m : Std.HashMap Name Nat := ∅
  for h : i in [0:env.header.moduleData.size] do
    let md := env.header.moduleData[i]
    for h' : j in [0:md.constNames.size] do
      m := m.insert md.constNames[j] (i * 10000000 + j)
  return m

def isTargetModule (mod : Name) : Bool :=
  targetModulePrefixes.any (·.isPrefixOf mod)

def isEqnLemma : Name → Bool
  | .str _ s => s == "eq_def" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

/-- The target pool, sorted by name hash for a deterministic pseudo-random sample. -/
def candidates (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for h : i in [0:env.header.moduleData.size] do
    let mod := env.header.moduleNames[i]!
    unless isTargetModule mod do continue
    for n in env.header.moduleData[i].constNames do
      -- Generated equation lemmas (`f.eq_1`, `f.eq_def`) are unfolding rules nobody states
      -- as a goal; they can also be realized in several modules, hence the dedup.
      if isEqnLemma n || out.contains n then continue
      match env.find? n with
      | some (.thmInfo _) =>
          if !(isBlacklisted n || isNoise n) then out := out.push n
      | _ => pure ()
  return out.qsort fun a b =>
    let ha := mixHash (hash a) 0x9e3779b97f4a7c15
    let hb := mixHash (hash b) 0x9e3779b97f4a7c15
    if ha == hb then a.lt b else ha < hb

structure Row where
  name          : Name
  module        : Name
  status        : String   -- solved | unsolved | encode_error | error
  solver        : String := "-"
  millis        : Nat := 0
  coreSize      : Nat := 0
  reconstructed : Bool := false
  note          : String := ""

def Row.tsv (r : Row) : String :=
  let clean (s : String) := (s.replace "\t" " ").replace "\n" " " |>.take 200 |>.toString
  s!"{r.name}\t{r.module}\t{r.status}\t{r.solver}\t{r.millis}\t{r.coreSize}\t\
    {r.reconstructed}\t{clean r.note}"

def header : String :=
  "name\tmodule\tstatus\tsolver\tms\tcore\treconstructed\tnote\twall_ms"

/-- Kernel-check a closed proof of `type`, without keeping the declaration. -/
def kernelOk (type value : Expr) : MetaM Bool := do
  let value ← instantiateMVars value
  if value.hasMVar || value.hasSorry then return false
  if value.getUsedConstants.contains ``Hammer.trustSMT then return false
  let s ← saveState
  try
    addDecl (.thmDecl { name := `_hammerBench_check, levelParams := [], type, value })
    s.restore
    return true
  catch _ =>
    s.restore
    return false

def runOne (cfg : Hammer.Config) (pos : Std.HashMap Name Nat) (pool : Array Fact)
    (n : Name) : TermElabM Row := do
  let env ← getEnv
  let some ci := env.find? n | return { name := n, module := .anonymous, status := "error" }
  let module := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·.toNat]?)
    |>.getD .anonymous
  let base : Row := { name := n, module, status := "error" }
  let some myPos := pos[n]? | return { base with note := "no position" }
  let type := ci.type.instantiateLevelParams ci.levelParams (ci.levelParams.map fun _ => Level.one)
  -- Chronological premise pool: strictly earlier declarations only.
  let pool := pool.filter fun f => match pos[f.name]? with
    | some p => p < myPos
    | none => false
  let s ← saveState
  try
    let top ← mkFreshExprMVar type
    let (_, g) ← top.mvarId!.intros
    let row ← g.withContext do
      let goalType ← instantiateMVars (← g.getType)
      unless ← isProp goalType do return { base with note := "goal not a Prop" }
      let locals ← collectLocalFacts g
      let goalSyms := locals.foldl (init := featuresOf goalType) fun acc f =>
        f.symbols.fold (init := acc) fun a s => a.insert s
      let selected := selectPremises cfg goalSyms pool
      let types := (← collectGroundTypes (#[goalType] ++ locals.map (·.type))).take 8
      let mut facts := locals
      for f in selected do
        facts := facts ++ (← monomorphizeFact cfg f types)
      let allFacts := facts.take (cfg.maxPremises * 2)
      let enc ← try encodeProblem cfg goalType allFacts
        catch e => return { base with status := "encode_error", note := ← e.toMessageData.toString }
      let (attempts, _) ← solve cfg enc.text
      let some a := attempts.find? (fun a => a.result matches .unsat _)
        | let why := ", ".intercalate (attempts.toList.map fun a => s!"{a.backend}: {a.result.describe}")
          return { base with status := "unsolved", note := why }
      let core := match a.result with | .unsat c => c | _ => #[]
      let used := (core.filterMap fun l => enc.labels[l]?).foldl (init := #[]) fun acc x =>
        if acc.contains x then acc else acc.push x
      let solvedRow : Row :=
        { base with status := "solved", solver := a.backend, millis := a.millis, coreSize := used.size }
      -- On failure `duperReconstruct` restores the state, so the goal stays open.
      let remaining ← Tactic.run g do discard <| duperReconstruct cfg used
      let rec_ ← if remaining.isEmpty then kernelOk type top else pure false
      return { solvedRow with reconstructed := rec_ }
    s.restore
    return row
  catch e =>
    let msg ← e.toMessageData.toString
    s.restore
    return { base with note := msg }

/-- Also catch runtime exceptions (heartbeats, deep recursion) so one target cannot kill
the run. -/
def runOneSafe (cfg : Hammer.Config) (pos : Std.HashMap Name Nat) (pool : Array Fact)
    (n : Name) : TermElabM Row := do
  let s ← saveState
  tryCatchRuntimeEx (Core.withCurrHeartbeats (runOne cfg pos pool n)) fun e => do
    let msg ← e.toMessageData.toString
    s.restore
    return { name := n, module := .anonymous, status := "error", note := msg }

def getNat (var : String) (dflt : Nat) : IO Nat := do
  return ((← IO.getEnv var).bind (·.toNat?)).getD dflt

def main : TermElabM Unit := do
  let n ← getNat "BENCH_N" 200
  let shard ← getNat "BENCH_SHARD" 0
  let shards ← getNat "BENCH_SHARDS" 1
  let out := (← IO.getEnv "BENCH_OUT").getD "bench-results.tsv"
  let dflt : Hammer.Config := {}
  let cfg : Hammer.Config := { dflt with timeout := ← getNat "BENCH_TIMEOUT" dflt.timeout }
  let env ← getEnv
  let pos := positionMap env
  let pool ← collectGlobalFacts
  let all := candidates env
  let sample := (all.take n).toList.zipIdx.filter (fun (_, i) => i % shards == shard) |>.map (·.1)
  IO.println s!"candidates: {all.size}, sample: {min n all.size}, this shard: {sample.length}"
  let h ← IO.FS.Handle.mk out .write
  h.putStrLn header
  for t in sample do
    let t0 ← IO.monoMsNow
    let r ← withOptions (fun o => o.set `maxHeartbeats 2000000) <| runOneSafe cfg pos pool t
    let dt := (← IO.monoMsNow) - t0
    h.putStrLn s!"{r.tsv}\t{dt}"
    h.flush
    IO.println s!"{r.status}{if r.reconstructed then "+rec" else ""}\t{dt}ms\t{t}"

end HammerBench

#eval HammerBench.main
