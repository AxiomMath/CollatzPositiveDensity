/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02DevY
public import CollatzPosDens.Transfer.S02Uv
public import CollatzPosDens.Transfer.S02Xl
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The vertical deviation error bounds the vertical tail

For every Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the vertical tail of the fresh deviation mass
is bounded by `y_dv(ι) ^ (-X_l(ι, 0))`, where `y_dv` is the vertical generating-function point
`CollatzPosDens.devY` and `X_l` is the vertical allowance `CollatzPosDens.Xl`. This file shows
that `y_dv(ι) ^ (-X_l(ι, 0)) ≤ U_v(ι)`, where `U_v` is the vertical deviation error
`CollatzPosDens.Uv`.

Since `y_dv(o) = 169/168`, `X_l(o, 0) = 1503`, `y_dv(b) = 144/143` and `X_l(b, 0) = 1174`, the
inequality is the exact integer comparison `168^1503 · 10^20 ≤ 13370061336019939 · 169^1503` for
`ι = o` and `143^1174 · 10^20 ≤ 27986092430721741 · 144^1174` for `ι = b`; indeed
`(168/169)^1503 = 0.000133700613360199382…`, `(143/144)^1174 = 0.000279860924307217400…`, and
`U_v(ι)` is the twenty-digit decimal ceiling of the respective value.

## Main results

* `CollatzPosDens.devY_rpow_neg_Xl_zero_o`, `CollatzPosDens.devY_rpow_neg_Xl_zero_b`:
  `y_dv(o) ^ (-X_l(o, 0)) = (168/169)^1503` and `y_dv(b) ^ (-X_l(b, 0)) = (143/144)^1174` in `ℝ`.
* `CollatzPosDens.devY_inv_pow_le_Uv_o`, `CollatzPosDens.devY_inv_pow_le_Uv_b`:
  `(168/169)^1503 ≤ U_v(o)` and `(143/144)^1174 ≤ U_v(b)` in `ℚ`.
* `CollatzPosDens.devY_rpow_neg_Xl_zero_le_Uv`: `y_dv(ι) ^ (-X_l(ι, 0)) ≤ U_v(ι)` in `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The vertical tail bound at the original index: `y_dv(o) ^ (-X_l(o, 0)) = (168/169)^1503`. -/
theorem devY_rpow_neg_Xl_zero_o :
    (devY .o : ℝ) ^ (-(Xl .o 0 : ℝ)) = (168 / 169 : ℝ) ^ 1503 := by
  rw [Xl_zero_o, devY_cast_o, Rat.cast_ofNat, Real.rpow_neg (by norm_num),
    show ((1503 : ℝ)) = ((1503 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
  norm_num

/-- The vertical tail bound at the bootstrap index: `y_dv(b) ^ (-X_l(b, 0)) = (143/144)^1174`. -/
theorem devY_rpow_neg_Xl_zero_b :
    (devY .b : ℝ) ^ (-(Xl .b 0 : ℝ)) = (143 / 144 : ℝ) ^ 1174 := by
  rw [Xl_zero_b, devY_cast_b, Rat.cast_ofNat, Real.rpow_neg (by norm_num),
    show ((1174 : ℝ)) = ((1174 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
  norm_num

/-- The rational comparison `(168/169)^1503 ≤ U_v(o)`. -/
theorem devY_inv_pow_le_Uv_o : (168 / 169 : ℚ) ^ 1503 ≤ Uv .o := by
  have h : (168 : ℕ) ^ 1503 * 10 ^ 20 ≤ 13370061336019939 * 169 ^ 1503 := by decide +kernel
  rw [Uv_o, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

/-- The rational comparison `(143/144)^1174 ≤ U_v(b)`. -/
theorem devY_inv_pow_le_Uv_b : (143 / 144 : ℚ) ^ 1174 ≤ Uv .b := by
  have h : (143 : ℕ) ^ 1174 * 10 ^ 20 ≤ 27986092430721741 * 144 ^ 1174 := by decide +kernel
  rw [Uv_b, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

/-- The vertical deviation error bounds the vertical tail: `y_dv(ι) ^ (-X_l(ι, 0)) ≤ U_v(ι)`. -/
@[collatz_pos_dens "lem_s02_Uv"]
theorem devY_rpow_neg_Xl_zero_le_Uv (ι : FIndex) :
    (devY ι : ℝ) ^ (-(Xl ι 0 : ℝ)) ≤ (Uv ι : ℝ) := by
  cases ι
  · rw [devY_rpow_neg_Xl_zero_o]
    have h := (Rat.cast_le (K := ℝ)).2 devY_inv_pow_le_Uv_o
    simpa using h
  · rw [devY_rpow_neg_Xl_zero_b]
    have h := (Rat.cast_le (K := ℝ)).2 devY_inv_pow_le_Uv_b
    simpa using h

end CollatzPosDens
