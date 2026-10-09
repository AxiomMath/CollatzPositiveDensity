/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Syracuse
public import CollatzPosDens.Maps.InverseOrbitOdd

/-!
# The Syracuse map inverts the inverse orbit

Let `R` be a positive odd integer and `w = (a₁, …, a_d)` a word admissible from `R`. Then the
Syracuse map undoes each inverse step: `S(R_i) = R_{i-1}` for `1 ≤ i ≤ d`.

Every term of the inverse orbit is a positive odd integer, and `3 R_i + 1 = 2 ^ {a_i} R_{i-1}`
with `R_{i-1}` odd, so `v₂(3 R_i + 1) = a_i` and `S(R_i) = (3 R_i + 1) / 2 ^ {a_i} = R_{i-1}`.

## Main results

* `CollatzPosDens.collatzAccel_eq_of_three_mul_add_one_eq`: if `3x + 1 = 2 ^ a y` with `y` odd,
  then `S(x) = y`.
* `CollatzPosDens.Admissible.collatzAccel_inverseOrbit_succ`: along an admissible word from a
  positive odd integer, `S(R_{i+1}) = R_i` for `i < d`.

## Implementation notes

The Syracuse map is a function on `ℕ` while the inverse orbit takes values in `ℚ`, so the
statement asserts that `R_{i+1}` is the image of a natural number `m` and that `S(m)`, cast to
`ℚ`, is `R_i`. The index is shifted: the statement is indexed by `i + 1` with `i < d` in place
of `i` with `1 ≤ i ≤ d`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `3x + 1 = 2 ^ a y` with `y` odd, then the Syracuse map sends `x` to `y`. -/
theorem collatzAccel_eq_of_three_mul_add_one_eq {x y a : ℕ} (h : 3 * x + 1 = 2 ^ a * y)
    (hy : Odd y) : collatzAccel x = y := by
  have hy0 : y ≠ 0 := hy.pos.ne'
  have hv : padicValNat 2 (3 * x + 1) = a := by
    rw [h, padicValNat.mul (pow_ne_zero _ two_ne_zero) hy0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hy)), add_zero]
  rw [collatzAccel_def, hv, h, Nat.mul_div_cancel_left _ (pow_pos two_pos _)]

/-- If `R` is a positive odd integer and `w` is admissible from `R`, then for `i < |w|` the term
`R_{i+1}` of the inverse orbit is a natural number `m` with `S(m) = R_i`. -/
@[collatz_pos_dens "lem_syracuse_of_inverse"]
theorem Admissible.collatzAccel_inverseOrbit_succ {R : ℤ} {w : Word}
    (hw : Admissible R w) (hpos : 0 < R) (hodd : Odd R) {i : ℕ} (hi : i < w.length) :
    ∃ m : ℕ, inverseOrbit w R (i + 1) = m ∧ (collatzAccel m : ℚ) = inverseOrbit w R i := by
  obtain ⟨m, hm, hmpos, hmodd⟩ := hw.exists_inverseOrbit_eq_pos_odd hpos hodd hi
  obtain ⟨k, hk, hkpos, hkodd⟩ := hw.exists_inverseOrbit_eq_pos_odd hpos hodd hi.le
  lift m to ℕ using hmpos.le
  lift k to ℕ using hkpos.le
  refine ⟨m, by exact_mod_cast hm, ?_⟩
  rw [inverseOrbit_succ w R hi, hk, invStep] at hm
  have h : 3 * m + 1 = 2 ^ (w[i] : ℕ) * k := by
    push_cast at hm
    have : ((3 * m + 1 : ℕ) : ℚ) = ((2 ^ (w[i] : ℕ) * k : ℕ) : ℚ) := by
      push_cast
      rw [← hm]
      ring
    exact_mod_cast this
  rw [collatzAccel_eq_of_three_mul_add_one_eq h (by exact_mod_cast hkodd), hk]
  rfl

end CollatzPosDens
