import Lean

/-!
# LeanHammer — 基础类型与配置

本文件定义 hammer 全流程共享的配置、结果类型，以及用于"无重建"收尾的信任公理。
-/

namespace Hammer

open Lean

/-- 外部 SMT 求解器的后端描述。 -/
structure Backend where
  /-- 用于报告和 `solvers` 配置的名字，例如 `"z3"`。 -/
  name    : String
  /-- 可执行文件名（在 `PATH` 上查找）。 -/
  exe     : String
  /-- 生成命令行参数：给定超时（秒）和问题文件路径。 -/
  args    : Nat → System.FilePath → Array String
  deriving Inhabited

/-- `hammer` 的配置。 -/
structure Config where
  /-- 前提选择后交给求解器的最大引理数。 -/
  maxPremises  : Nat := 96
  /-- 每个求解器的墙钟超时（秒）。 -/
  timeout      : Nat := 10
  /-- 要并行竞速的后端名字。 -/
  solvers      : List String := ["z3", "cvc5"]
  /-- 打印 SMT-LIB 问题与求解器原始输出。 -/
  verbose      : Bool := false
  /-- 请求 unsat core，用于报告"真正用到的前提"。 -/
  unsatCores   : Bool := true
  /-- 对多态引理做单态化实例化。 -/
  monomorphize : Bool := true
  /-- 单态化时每条引理最多产生多少个实例。 -/
  maxInstances : Nat := 8
  /-- 若为 `false`，只报告不闭合目标。 -/
  closeGoal    : Bool := true
  /--
  拿到 unsat core 后，尝试用 Duper 在 Lean 内部重证一遍。

  成功则目标由真正的证明项闭合，不沾 `trustSMT`；失败就退回信任公理。
  这是"外包版"的逆向翻译：外部求解器负责搜索，Duper 负责重建。
  需要导入 `Hammer.Reconstruct` 才会生效。
  -/
  reconstruct  : Bool := true
  /-- 单次 Duper 重建的心跳预算。 -/
  reconstructHeartbeats : Nat := 400000
  /--
  允许为"无法确认非空"的 Lean 类型声明不解释排序。

  SMT-LIB 假设每个排序非空，而 Lean 的类型可以是空的：`∀ x : Empty, P x` 在 Lean 里
  平凡为真，翻成 SMT 却成了一条实打实的断言。默认 (`false`) 要求 `Nonempty` 可合成，
  宁可丢前提也不冒险；置 `true` 换取覆盖面，但 `unsat` 不再可信。
  -/
  assumeNonempty : Bool := false
  deriving Inhabited, Repr

/-- 求解器对一个问题的回答。 -/
inductive SolverResult where
  /-- 问题不可满足：目标成立。`core` 是 unsat core 中的断言名。 -/
  | unsat (core : Array String)
  /-- 问题可满足：目标（在本次编码下）不成立。 -/
  | sat
  /-- 超时、内存不足或求解器放弃。 -/
  | unknown (reason : String)
  /-- 调用求解器本身失败（未安装、崩溃等）。 -/
  | error (msg : String)
  deriving Inhabited, Repr

/--
信任公理。当外部 SMT 求解器判定 `¬ p` 与选出的前提不可满足时，`hammer` 用它闭合目标。

**它不是一个证明。** 这条公理让 `p` 无条件成立，因此靠它闭合的定理都会在
`#print axioms` 里显示 `Hammer.trustSMT`。

只有在逆向翻译失败时才会走到这里。导入 `Hammer.Reconstruct` 后，`hammer` 会先把
unsat core 交给 Duper 在 Lean 内部重证；成功的话目标由真证明项闭合，这条公理不出现。
Duper 没有算术决策过程，所以纯算术目标目前仍会落到这里。
-/
axiom trustSMT (p : Prop) : p

end Hammer
