import Hammer

/-!
# `hammer` 能证的例子

每个 `example` 都靠 `hammer` 闭合。注意闭合用的是 `Hammer.trustSMT`，
所以这些不是证明——它们检验的是"前 4 步是否把问题正确地送到了求解器手里"。
-/

set_option maxHeartbeats 2000000

namespace HammerTest

/-! ## 线性算术 -/

example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by hammer
example (x y : Int) (h : x < y) : x + 1 ≤ y := by hammer
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by hammer
example (x y z : Int) (h : x + y = z) : x = z - y := by hammer

/-! ## `Nat` 的全函数语义 -/

-- 截断减法
example (n : Nat) : n - (n + 1) = 0 := by hammer
example (a b : Nat) (h : b ≤ a) : a - b + b = a := by hammer
-- 除以零
example (n : Nat) : n / 0 = 0 := by hammer
example (n : Nat) : n % 0 = n := by hammer
-- Lean 的 `Int` 除法就是 SMT 的欧几里得 `div`
example : (-7 : Int) / 2 = -4 := by hammer

/-! ## 命题逻辑 -/

example (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by hammer
example (p q : Prop) (h : ¬(p ∨ q)) : ¬p ∧ ¬q := by hammer
example (p q : Prop) (h : p ↔ q) (hp : p) : q := by hammer

/-! ## 不解释函数与等式 -/

example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by hammer
example (f : Nat → Nat) (h : ∀ n, f n = n + 1) : f 3 = 4 := by hammer
example (f : Nat → Nat → Nat) (a b : Nat)
    (hc : ∀ x y, f x y = f y x) : f a b = f b a := by hammer

/-! ## 量词 -/

example (P : Nat → Prop) (h : ∀ n, P n) : P 7 := by hammer
example (P : Nat → Prop) (h : P 3) : ∃ n, P n := by hammer

/-! ## 需要从 environment 里捞引理（而不是靠算术） -/

example (l₁ l₂ : List Nat) : (l₁ ++ l₂).length = l₁.length + l₂.length := by hammer
example (l : List Nat) : ([] ++ l).length = l.length := by hammer

end HammerTest
