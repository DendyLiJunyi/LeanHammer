import Hammer.Tactic
import Duper.Tactic

/-!
# 逆向翻译（外包给 Duper）

外部 SMT 求解器给出的 unsat core 说明"这几条前提足以推出目标"，但它不给 Lean 能检查的
证明。Duper 是一个跑在 Lean 里的 superposition 证明器，产出真正的证明项——于是最省事的
逆向翻译就是：**把 core 里的引理交给 Duper，让它在 Lean 内部重证一遍**。

这条路子的分工是 hammer 的经典形态：外部求解器负责在几万条引理里**搜索**，
Duper 负责在几条引理上**重建**。搜索空间被 core 砍到个位数之后，Duper 往往就够用了。

## 覆盖面的落差

Duper 是纯一阶等式推理，**没有算术决策过程**。凡是靠 z3 的线性算术判定出来的目标
（`a ≤ b → a ≤ b + 1`、`n - (n+1) = 0`），core 里往往只有一两条假设，剩下的工作全在
求解器的算术理论里——这部分 Duper 接不住。能顺利转手的是纯等式/一阶推理的目标。

导入本模块即自动生效；`hammer (reconstruct := false)` 可以关掉。
-/

namespace Hammer

open Lean Elab Tactic Meta

/-- 用 unsat core 里的引理调 Duper。`*` 让 Duper 自己收集局部上下文。 -/
def duperReconstruct (cfg : Hammer.Config) (used : Array Name) : TacticM Bool := do
  let env ← getEnv
  -- 局部假设由 `*` 带进来，这里只补全局引理；`mkCIdent` 预解析，绕开命名空间与遮蔽。
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
    -- Duper 是 terminal tactic：跑通就意味着目标已闭合。
    return true
  catch _ =>
    s.restore
    return false

initialize reconstructHook.set (some duperReconstruct)

end Hammer
