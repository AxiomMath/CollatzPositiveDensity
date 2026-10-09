/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Ring.Parity
public import CollatzPosDens.Definitions

/-!
# The Collatz map

Basic facts about the Collatz map `CollatzPosDens.collatz`, which sends an even `n` to `n / 2`
and an odd `n` to `3 * n + 1`. Its value at `0` is `0 / 2 = 0`, so `0` is a fixed point.

## Main results

* `CollatzPosDens.collatz_of_even`, `CollatzPosDens.collatz_of_odd`: the two branches.
* `CollatzPosDens.collatz_zero`: `0` is fixed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- On `n` with `n % 2 = 0` the Collatz map halves. -/
theorem collatz_of_mod_two_eq_zero {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

/-- On `n` with `n % 2 = 1` the Collatz map is `n ↦ 3n + 1`. -/
theorem collatz_of_mod_two_eq_one {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, h]

/-- On even `n` the Collatz map halves. -/
theorem collatz_of_even {n : ℕ} (h : Even n) : collatz n = n / 2 :=
  collatz_of_mod_two_eq_zero (Nat.even_iff.mp h)

/-- On odd `n` the Collatz map is `n ↦ 3n + 1`. -/
theorem collatz_of_odd {n : ℕ} (h : Odd n) : collatz n = 3 * n + 1 :=
  collatz_of_mod_two_eq_one (Nat.odd_iff.mp h)

/-- `0` is a fixed point of the Collatz map. -/
@[simp]
theorem collatz_zero : collatz 0 = 0 := rfl

/-- The Collatz map sends `2n` to `n`. -/
@[simp]
theorem collatz_two_mul (n : ℕ) : collatz (2 * n) = n := by
  rw [collatz_of_mod_two_eq_zero (by omega)]; omega

/-- The Collatz map sends `2n + 1` to `6n + 4`. -/
@[simp]
theorem collatz_two_mul_add_one (n : ℕ) : collatz (2 * n + 1) = 6 * n + 4 := by
  rw [collatz_of_mod_two_eq_one (by omega)]; omega

end CollatzPosDens
