import Hammer

/-!
# Measuring reconstruction coverage

The same goals as `HammerTest/Basic.lean`, but as named theorems so `#print axioms` can
tell us how each one was closed:

* `Hammer.trustSMT` present: Duper could not rebuild it; the trust axiom closed the goal.
* only `propext / Classical.choice / Quot.sound`: Duper rebuilt it, and this is a real
  proof.
-/

set_option maxHeartbeats 4000000

namespace HammerTest.Reconstruct

theorem a01 (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by hammer
theorem a02 (x y : Int) (h : x < y) : x + 1 ≤ y := by hammer
theorem a03 (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by hammer
theorem a04 (x y z : Int) (h : x + y = z) : x = z - y := by hammer

theorem n01 (n : Nat) : n - (n + 1) = 0 := by hammer
theorem n02 (a b : Nat) (h : b ≤ a) : a - b + b = a := by hammer
theorem n03 (n : Nat) : n / 0 = 0 := by hammer
theorem n04 (n : Nat) : n % 0 = n := by hammer
theorem n05 : (-7 : Int) / 2 = -4 := by hammer

theorem p01 (p q r : Prop) (h1 : p → q) (h2 : q → r) (hp : p) : r := by hammer
theorem p02 (p q : Prop) (h : ¬(p ∨ q)) : ¬p ∧ ¬q := by hammer
theorem p03 (p q : Prop) (h : p ↔ q) (hp : p) : q := by hammer

theorem u01 (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by hammer
theorem u02 (f : Nat → Nat) (h : ∀ n, f n = n + 1) : f 3 = 4 := by hammer
theorem u03 (f : Nat → Nat → Nat) (a b : Nat)
    (hc : ∀ x y, f x y = f y x) : f a b = f b a := by hammer

theorem q01 (P : Nat → Prop) (h : ∀ n, P n) : P 7 := by hammer
theorem q02 (P : Nat → Prop) (h : P 3) : ∃ n, P n := by hammer

theorem e01 (l₁ l₂ : List Nat) : (l₁ ++ l₂).length = l₁.length + l₂.length := by hammer
theorem e02 (l : List Nat) : ([] ++ l).length = l.length := by hammer

#print axioms a01
#print axioms a02
#print axioms a03
#print axioms a04
#print axioms n01
#print axioms n02
#print axioms n03
#print axioms n04
#print axioms n05
#print axioms p01
#print axioms p02
#print axioms p03
#print axioms u01
#print axioms u02
#print axioms u03
#print axioms q01
#print axioms q02
#print axioms e01
#print axioms e02

end HammerTest.Reconstruct
