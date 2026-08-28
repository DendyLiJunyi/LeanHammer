import Hammer

/-!
# Goals `hammer` can discharge

Every `example` here is closed by `hammer`. What they check is that the search half of the
pipeline hands the solver a correct problem. Whether the goal ends up closed by a real
proof term or by the trust axiom is measured separately, in `HammerTest/Reconstruct.lean`.
-/

set_option maxHeartbeats 2000000

namespace HammerTest

/-! ## Linear arithmetic -/

example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by hammer
example (x y : Int) (h : x < y) : x + 1 ≤ y := by hammer
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by hammer
example (x y z : Int) (h : x + y = z) : x = z - y := by hammer

/-! ## `Nat`'s total-function semantics -/

-- Truncated subtraction
example (n : Nat) : n - (n + 1) = 0 := by hammer
example (a b : Nat) (h : b ≤ a) : a - b + b = a := by hammer
-- Division by zero
example (n : Nat) : n / 0 = 0 := by hammer
example (n : Nat) : n % 0 = n := by hammer
-- Lean's `Int` division is exactly SMT's Euclidean `div`
example : (-7 : Int) / 2 = -4 := by hammer

/-! ## Propositional logic -/

example (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by hammer
example (p q : Prop) (h : ¬(p ∨ q)) : ¬p ∧ ¬q := by hammer
example (p q : Prop) (h : p ↔ q) (hp : p) : q := by hammer

/-! ## Uninterpreted functions and equality -/

example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by hammer
example (f : Nat → Nat) (h : ∀ n, f n = n + 1) : f 3 = 4 := by hammer
example (f : Nat → Nat → Nat) (a b : Nat)
    (hc : ∀ x y, f x y = f y x) : f a b = f b a := by hammer

/-! ## Quantifiers -/

example (P : Nat → Prop) (h : ∀ n, P n) : P 7 := by hammer
example (P : Nat → Prop) (h : P 3) : ∃ n, P n := by hammer

/-! ## Goals needing a lemma from the environment, not just arithmetic -/

example (l₁ l₂ : List Nat) : (l₁ ++ l₂).length = l₁.length + l₂.length := by hammer
example (l : List Nat) : ([] ++ l).length = l.length := by hammer

end HammerTest
