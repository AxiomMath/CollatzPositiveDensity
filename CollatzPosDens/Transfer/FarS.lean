/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dsc
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Far scales dominate the far-gap scale

For every real `m ≥ D_sc` we have `m / (log m)^2 > S_*`, where `S_*` is the far-gap scale and
`D_sc` the scale threshold of the analytic recipe.

This follows from a general estimate: if `m > 1` and `(16 S)^2 ≤ m` then `S < m / (log m)^2`.
Indeed, writing `m = y^4` with `y = m^{1/4} ≥ 1`, the inequality `log y ≤ y - 1` gives
`0 < log m = 4 log y < 4 y`, so `S (log m)^2 < 16 S y^2 = 16 S √m ≤ m`. Since
`D_sc ≥ (100 S_*)^2 ≥ (16 S_*)^2` and `D_sc ≥ 2`, the threshold statement follows.

## Main results

* `CollatzPosDens.sStar_lt_div_log_sq_of_sq_le`: if `1 < m` and `(16 S)^2 ≤ m` then
  `S < m / (log m)^2`.
* `CollatzPosDens.sStar_lt_div_log_sq`: for every real `m ≥ D_sc`, `S_* < m / (log m)^2`.

## Implementation notes

[mazur2026] argues via monotonicity of `x ↦ x / (log x)^2` on `[e^2, ∞)` and the numerical
bounds `log (10^4) < 10` and `log S_* < √S_*`, comparing with `m₀ = (100 S_*)^2`. Here instead
the elementary bound `log y ≤ y - 1` is applied to `y = m^{1/4}` directly at `m`, which avoids
both the monotonicity argument and the numerical estimates, and needs only `(16 S_*)^2 ≤ m`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `1 < m` and `(16 S)^2 ≤ m`, then `S < m / (log m)^2`. -/
theorem sStar_lt_div_log_sq_of_sq_le {S m : ℝ} (hm : 1 < m) (h : (16 * S) ^ 2 ≤ m) :
    S < m / Real.log m ^ 2 := by
  set y := Real.sqrt (Real.sqrt m)
  have hy2 : y ^ 2 = Real.sqrt m := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hy4 : y ^ 4 = m := by
    rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hy2, Real.sq_sqrt (by positivity)]
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hm.le)
  have hlog : Real.log m = 4 * Real.log y := by
    rw [← hy4, Real.log_pow]
    norm_num
  have hly : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hly0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hlogpos : 0 < Real.log m := Real.log_pos hm
  rw [lt_div_iff₀ (by positivity)]
  rcases le_or_gt S 0 with hS | hS
  · nlinarith [sq_nonneg (Real.log m)]
  · have h16 : 16 * S ≤ y ^ 2 := hy2 ▸ Real.le_sqrt_of_sq_le h
    have hsq : Real.log y ^ 2 < y ^ 2 := by nlinarith
    calc S * Real.log m ^ 2 = 16 * S * Real.log y ^ 2 := by
          rw [hlog]
          ring
      _ < 16 * S * y ^ 2 := by gcongr
      _ ≤ y ^ 2 * y ^ 2 := by gcongr
      _ = m := by
          rw [← hy4]
          ring

/-- For every real `m ≥ Dsc`, `m / (log m)^2 > sStar`. -/
@[collatz_pos_dens "lem_s02_far_S"]
theorem sStar_lt_div_log_sq {m : ℝ} (hm : (Dsc : ℝ) ≤ m) :
    m / Real.log m ^ 2 > (sStar : ℝ) := by
  have h2 : (2 : ℝ) ≤ Dsc := by exact_mod_cast two_le_Dsc
  have hsq : (100 * (sStar : ℝ)) ^ 2 ≤ Dsc := by exact_mod_cast sq_hundred_sStar_le_Dsc
  have hS : (0 : ℝ) ≤ sStar := Nat.cast_nonneg _
  refine sStar_lt_div_log_sq_of_sq_le (by linarith) ?_
  nlinarith

end CollatzPosDens
