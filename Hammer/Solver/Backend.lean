import Hammer.Basic
import Hammer.Translate.SMTLib

/-!
# 外部求解器的调用与结果解析

把 SMT-LIB 文本写到临时文件，并行跑所有配置的后端，取第一个给出 `unsat` 的。
超时由求解器自己的选项负责，所以即使我们提前返回，遗留进程也会在超时后自杀。
-/

namespace Hammer

open Lean

/-- 内置后端表。`hammer` 的 `solvers` 配置按 `name` 在这里查。 -/
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

/-- 在系统临时目录下造一个唯一的 `.smt2` 路径。 -/
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

/-- 从求解器输出里抠出 unsat core 的标签。 -/
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

/-- 解析 z3 / cvc5 的标准输出。 -/
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
  return .unknown "求解器没有给出 sat/unsat/unknown"

/-- 结果的可读摘要，用于 `verbose` 报告。 -/
def SolverResult.describe : SolverResult → String
  | .unsat core => s!"unsat (core 大小 {core.size})"
  | .sat => "sat"
  | .unknown r => s!"unknown: {r}"
  | .error m => s!"error: {m}"

/-- 跑单个后端。任何异常都收敛成 `.error`。 -/
def runBackend (b : Backend) (timeout : Nat) (path : System.FilePath) :
    BaseIO SolverResult := do
  let act : IO SolverResult := do
    let out ← IO.Process.output { cmd := b.exe, args := b.args timeout path }
    return parseOutput out.stdout out.stderr out.exitCode
  match ← act.toBaseIO with
  | .ok r => return r
  | .error e => return .error s!"无法运行 {b.exe}: {e}"

/-- 一次求解的完整记录，供报告使用。 -/
structure Attempt where
  backend : String
  result  : SolverResult
  millis  : Nat

/--
把问题喂给所有后端并行竞速。返回全部尝试记录（第一个 `unsat` 出现后不再等待余下的）。
`problemText` 会被写到临时文件，路径一并返回以便 `verbose` 时提示。
-/
def solve (cfg : Config) (problemText : String) :
    IO (Array Attempt × System.FilePath) := do
  let path ← freshProblemPath
  IO.FS.writeFile path problemText
  let backends := cfg.solvers.filterMap backendByName? |>.toArray
  if backends.isEmpty then
    return (#[⟨"<none>", .error "没有可用后端；检查 solvers 配置", 0⟩], path)
  let start ← IO.monoMsNow
  let tasks ← backends.mapM fun b =>
    return (b.name, ← BaseIO.asTask (runBackend b cfg.timeout path))
  -- 轮询：一旦有人报 unsat 就立刻返回。
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
