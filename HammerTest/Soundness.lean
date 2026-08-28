import Hammer

/-!
# 健全性回归

这里的每个命题都**不可证**（要么本身为假，要么前提不足）。`hammer` 必须报错。
它们守的是编码那一层：一个把真命题翻错成矛盾的编码，会让这些例子"证明成功"。

历史上被这些用例抓到的 bug：
* `Fin.pos : ∀ {n} (i : Fin n), 0 < n` —— 把依赖类型 `Fin n` 抽象成与 `n` 无关的
  排序，于是"Fin 非空 ⇒ 所有 n > 0"，整个问题自相矛盾。
-/

set_option maxHeartbeats 2000000

namespace HammerTest.Soundness

-- 为假：n = 0 时 `0 - 1 + 1 = 1 ≠ 0`
example (n : Nat) : n - 1 + 1 = n := by
  fail_if_success (hammer)
  sorry

-- 前提不足
example (a b : Nat) : a ≤ b := by
  fail_if_success (hammer (timeout := 3))
  sorry

-- 前提不足：f 是任意函数
example (f : Nat → Nat) (a b : Nat) : f a = f b := by
  fail_if_success (hammer (timeout := 3))
  sorry

-- 为假：Int 上没有非负性
example (x : Int) : 0 ≤ x := by
  fail_if_success (hammer (timeout := 3))
  sorry

-- 为假：Nat 减法截断，不能随便移项
example (a b : Nat) : a - b + b = a := by
  fail_if_success (hammer (timeout := 3))
  sorry

end HammerTest.Soundness
