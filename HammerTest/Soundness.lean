import Hammer

/-!
# Soundness regression

Every proposition below is **unprovable** -- either outright false, or not entailed by its
hypotheses. `hammer` must fail on all of them.

These guard the encoder. An encoding that turns a true statement into a contradiction
would make these examples "succeed".

A bug actually caught this way:
* `Fin.pos : ∀ {n} (i : Fin n), 0 < n`. Abstracting the dependent type `Fin n` into a sort
  independent of `n` yields "Fin is nonempty ⇒ every n > 0", making the whole problem
  self-contradictory.
-/

set_option maxHeartbeats 2000000

namespace HammerTest.Soundness

-- False: at n = 0, `0 - 1 + 1 = 1 ≠ 0`
example (n : Nat) : n - 1 + 1 = n := by
  fail_if_success (hammer)
  sorry

-- Not entailed
example (a b : Nat) : a ≤ b := by
  fail_if_success (hammer (timeout := 3))
  sorry

-- Not entailed: f is an arbitrary function
example (f : Nat → Nat) (a b : Nat) : f a = f b := by
  fail_if_success (hammer (timeout := 3))
  sorry

-- False: there is no non-negativity on Int
example (x : Int) : 0 ≤ x := by
  fail_if_success (hammer (timeout := 3))
  sorry

-- False: `Nat` subtraction truncates, so you cannot just move terms across
example (a b : Nat) : a - b + b = a := by
  fail_if_success (hammer (timeout := 3))
  sorry

end HammerTest.Soundness
