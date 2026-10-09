/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Logic.Function.Iterate
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Collatz
public import CollatzPosDens.Maps.InverseOrbitOdd

/-!
# The Collatz map undoes an inverse step

Let `R` be a positive odd integer and `w = (a₁, …, a_d)` admissible from `R`, with inverse orbit
`R₀, …, R_d`. Then `T ^ {1 + a_i} (R_i) = R_{i-1}` for `1 ≤ i ≤ d`: since `R_i` is odd,
`T(R_i) = 3 R_i + 1 = 2 ^ {a_i} R_{i-1}`, and `a_i` halvings bring this back to `R_{i-1}`.

## Main results

* `CollatzPosDens.collatz_iterate_two_pow_mul`: `T ^ k (2 ^ k y) = y`.
* `CollatzPosDens.Admissible.exists_collatz_iterate_inverseOrbit`: along an admissible word,
  `R_i` and `R_{i-1}` are natural numbers with `T ^ {1 + a_i} (R_i) = R_{i-1}`.

## Implementation notes

The inverse orbit lives in `ℚ` and the Collatz map on `ℕ`, so the statement asserts that the two
consecutive terms are (casts of) natural numbers related by the Collatz iterate. Words are
indexed from `0` in Lean: the letter `a_{i+1}` is `w[i]`, for `i < |w|`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §2.
-/

@[expose] public section

namespace CollatzPosDens

/-- `k` Collatz steps undo `k` doublings: `T ^ k (2 ^ k y) = y`. -/
theorem collatz_iterate_two_pow_mul (k y : ℕ) : collatz^[k] (2 ^ k * y) = y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, pow_succ', mul_assoc, collatz_two_mul, ih]

/-- If `R` is a positive odd integer and `w = (a₁, …, a_d)` is admissible from `R`, then for
`1 ≤ i ≤ d` the terms `R_i` and `R_{i-1}` of the inverse orbit are natural numbers with
`T ^ {1 + a_i} (R_i) = R_{i-1}`. Here `i` is shifted by one: `w[i] = a_{i+1}`. -/
@[collatz_pos_dens "lem_collatz_of_inverse"]
theorem Admissible.exists_collatz_iterate_inverseOrbit {R : ℤ} {w : Word}
    (hw : Admissible R w) (hpos : 0 < R) (hodd : Odd R) {i : ℕ} (hi : i < w.length) :
    ∃ m n : ℕ, inverseOrbit w R (i + 1) = m ∧ inverseOrbit w R i = n ∧
      collatz^[1 + (w[i] : ℕ)] m = n := by
  obtain ⟨m, hm, hmpos, hmodd⟩ := hw.exists_inverseOrbit_eq_pos_odd hpos hodd hi
  obtain ⟨n, hn, hnpos, -⟩ := hw.exists_inverseOrbit_eq_pos_odd hpos hodd hi.le
  lift m to ℕ using hmpos.le
  lift n to ℕ using hnpos.le
  refine ⟨m, n, by exact_mod_cast hm, by exact_mod_cast hn, ?_⟩
  have hrel : 3 * m + 1 = 2 ^ (w[i] : ℕ) * n := by
    have h := hm
    rw [inverseOrbit_succ w R hi, hn, invStep] at h
    have : ((3 * m + 1 : ℕ) : ℚ) = ((2 ^ (w[i] : ℕ) * n : ℕ) : ℚ) := by
      push_cast at h ⊢
      linarith
    exact_mod_cast this
  rw [add_comm, Function.iterate_add_apply, Function.iterate_one,
    collatz_of_odd (by exact_mod_cast hmodd), hrel, collatz_iterate_two_pow_mul]

end CollatzPosDens
