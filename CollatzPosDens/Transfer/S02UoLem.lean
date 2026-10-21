/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Uo
public import CollatzPosDens.Transfer.S02Xo
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order

/-!
# The overshoot deviation error bounds `9 (25/27)^{X_o(ι)}`

For every Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the overshoot deviation error `U_o(ι)` is an
upper bound for `9 (25/27)^{X_o(ι)}`, where `X_o(o) = 194` and `X_o(b) = 182` are the overshoot
allowances.

Clearing denominators, the claim is the integer comparison
`9 · 25^194 · 10^20 ≤ 295143990568991 · 27^194` for `ι = o` and
`9 · 25^182 · 10^20 ≤ 743222777209534 · 27^182` for `ι = b`, each decided by evaluation in `ℕ`.
Indeed `9 (25/27)^194 = 0.0000029514399056899006…`, `9 (25/27)^182 = 0.0000074322277720953316…`,
and `U_o(ι)` is the twenty-digit decimal ceiling of the respective value.

## Main results

* `CollatzPosDens.nine_mul_pow_overshootAllowance_le_Uo`: `9 (25/27)^{X_o(ι)} ≤ U_o(ι)` in `ℚ`.
* `CollatzPosDens.nine_mul_pow_overshootAllowance_le_Uo_cast`: the same bound in any linearly
  ordered field, e.g. `ℝ`, with `U_o(ι)` cast from `ℚ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The overshoot deviation error dominates `9 (25/27)^{X_o(ι)}`. -/
theorem nine_mul_pow_overshootAllowance_le_Uo (ι : FIndex) :
    9 * (25 / 27 : ℚ) ^ overshootAllowance ι ≤ Uo ι := by
  cases ι
  · have hint : (9 : ℕ) * 25 ^ 194 * 10 ^ 20 ≤ 295143990568991 * 27 ^ 194 := by
      decide +kernel
    rw [Uo_o, overshootAllowance_o, div_pow, ← mul_div_assoc,
      div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast hint
  · have hint : (9 : ℕ) * 25 ^ 182 * 10 ^ 20 ≤ 743222777209534 * 27 ^ 182 := by
      decide +kernel
    rw [Uo_b, overshootAllowance_b, div_pow, ← mul_div_assoc,
      div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast hint

/-- The overshoot deviation error dominates `9 (25/27)^{X_o(ι)}` in any linearly ordered
field. -/
@[collatz_pos_dens "lem_s02_Uo"]
theorem nine_mul_pow_overshootAllowance_le_Uo_cast {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (ι : FIndex) :
    9 * (25 / 27 : K) ^ overshootAllowance ι ≤ (Uo ι : K) := by
  have h := (Rat.cast_le (K := K)).2 (nine_mul_pow_overshootAllowance_le_Uo ι)
  push_cast at h
  exact h

end CollatzPosDens
