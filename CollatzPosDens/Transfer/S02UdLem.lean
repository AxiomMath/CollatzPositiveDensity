/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02DevB
public import CollatzPosDens.Transfer.S02Ud
public import CollatzPosDens.Transfer.S02Xd
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The drift-free deviation error bounds the deviation tail

For every Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the drift-free deviation tail is
`2 b_dv(ι) ^ (-4 X_d(ι, 0))`, where `b_dv` is the drift-free generating-function base and `X_d`
is the drift-free allowance. This file shows that it is bounded by the drift-free deviation error
`U_d(ι)`.

Since `b_dv(o) = 51/50`, `4 X_d(o, 0) = 524`, `b_dv(b) = 43/42` and `4 X_d(b, 0) = 408`, the tail
equals `2 (50/51)^524 = 0.0000623074521195470007…` for `ι = o` and
`2 (42/43)^408 = 0.000135397486279932862…` for `ι = b`, and the inequality is the exact integer
comparison `2 · 50^524 · 10^20 ≤ 6230745211954701 · 51^524`, respectively
`2 · 42^408 · 10^20 ≤ 13539748627993287 · 43^408`.

## Main results

* `CollatzPosDens.two_mul_fifty_div_fiftyOne_pow_le_Ud`: `2 (50/51)^524 ≤ U_d(o)` in `ℚ`.
* `CollatzPosDens.two_mul_fortyTwo_div_fortyThree_pow_le_Ud`: `2 (42/43)^408 ≤ U_d(b)` in `ℚ`.
* `CollatzPosDens.two_mul_devB_rpow_neg_Xd_zero_o`,
  `CollatzPosDens.two_mul_devB_rpow_neg_Xd_zero_b`:
  the values `2 b_dv(o) ^ (-4 X_d(o, 0)) = 2 (50/51)^524` and
  `2 b_dv(b) ^ (-4 X_d(b, 0)) = 2 (42/43)^408` in `ℝ`.
* `CollatzPosDens.Ud_bound`: `2 b_dv(ι) ^ (-4 X_d(ι, 0)) ≤ U_d(ι)` in `ℝ`, with a real exponent.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The rounded drift-free deviation error dominates `2 (50/51)^524`, as an inequality of
rationals; equivalently `2 · 50^524 · 10^20 ≤ 6230745211954701 · 51^524`. -/
theorem two_mul_fifty_div_fiftyOne_pow_le_Ud : 2 * (50 / 51 : ℚ) ^ 524 ≤ Ud .o := by
  rw [Ud_o, div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast (by decide +kernel :
    2 * 50 ^ 524 * 10 ^ 20 ≤ 6230745211954701 * 51 ^ 524)

/-- The rounded drift-free deviation error dominates `2 (42/43)^408`, as an inequality of
rationals; equivalently `2 · 42^408 · 10^20 ≤ 13539748627993287 · 43^408`. -/
theorem two_mul_fortyTwo_div_fortyThree_pow_le_Ud : 2 * (42 / 43 : ℚ) ^ 408 ≤ Ud .b := by
  rw [Ud_b, div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast (by decide +kernel :
    2 * 42 ^ 408 * 10 ^ 20 ≤ 13539748627993287 * 43 ^ 408)

/-- The drift-free deviation tail at the original index:
`2 b_dv(o) ^ (-4 X_d(o, 0)) = 2 (50/51)^524`. -/
theorem two_mul_devB_rpow_neg_Xd_zero_o :
    2 * (devB .o : ℝ) ^ (-(4 * (Xd .o 0 : ℝ))) = 2 * (50 / 51 : ℝ) ^ 524 := by
  rw [Xd_zero_o, devB_cast_o]
  have h : (-(4 * ((131 : ℚ) : ℝ))) = ((-524 : ℤ) : ℝ) := by push_cast; norm_num
  rw [h, Real.rpow_intCast, zpow_neg, ← inv_zpow, inv_div]
  rfl

/-- The drift-free deviation tail at the bootstrap index:
`2 b_dv(b) ^ (-4 X_d(b, 0)) = 2 (42/43)^408`. -/
theorem two_mul_devB_rpow_neg_Xd_zero_b :
    2 * (devB .b : ℝ) ^ (-(4 * (Xd .b 0 : ℝ))) = 2 * (42 / 43 : ℝ) ^ 408 := by
  rw [Xd_zero_b, devB_cast_b]
  have h : (-(4 * ((102 : ℚ) : ℝ))) = ((-408 : ℤ) : ℝ) := by push_cast; norm_num
  rw [h, Real.rpow_intCast, zpow_neg, ← inv_zpow, inv_div]
  rfl

/-- The drift-free deviation error: `2 b_dv(ι) ^ (-4 X_d(ι, 0)) ≤ U_d(ι)`, with the power taken
with a real exponent. -/
@[collatz_pos_dens "lem_s02_Ud"]
theorem Ud_bound (ι : FIndex) :
    2 * (devB ι : ℝ) ^ (-(4 * (Xd ι 0 : ℝ))) ≤ (Ud ι : ℝ) := by
  cases ι
  · rw [two_mul_devB_rpow_neg_Xd_zero_o]
    have h := (Rat.cast_le (K := ℝ)).mpr two_mul_fifty_div_fiftyOne_pow_le_Ud
    rwa [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat,
      Rat.cast_ofNat] at h
  · rw [two_mul_devB_rpow_neg_Xd_zero_b]
    have h := (Rat.cast_le (K := ℝ)).mpr two_mul_fortyTwo_div_fortyThree_pow_le_Ud
    rwa [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat,
      Rat.cast_ofNat] at h

end CollatzPosDens
