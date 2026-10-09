/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSignedFrac
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.CharSum.ChCosQuartic
public import CollatzPosDens.CharSum.ChExpCubic
public import CollatzPosDens.CharSum.ChFpFormula
public import CollatzPosDens.CharSum.ChRaw3Numeric
public import CollatzPosDens.CharSum.ChV0Lower

/-!
# Cancellation in a pair of white letters

Fix `n : ℕ` and `ξ ∈ G_n`. If the angle `ϑ = ϑ_{n,ξ}(j, s + 3)` satisfies `|ϑ| > 8 / 217`, then
the pair factor with `b = 3` is small: `Fp(j, s, 3) < exp(-21 / 3125)`.

With `φ = πϑ`, the formula for the pair factor gives
`Fp(j, s, 3) = ½ |1 + e^{-2iφ}| = |e^{-iφ} cos φ| = cos (π|ϑ|)`, since `|ϑ| ≤ ½`. The rational
angle `v∘ = 6283 / 54250` satisfies `0 < v∘ < 8π / 217 < π|ϑ| ≤ π / 2`, so
`cos (π|ϑ|) < cos v∘ ≤ 1 - v∘² / 2 + v∘⁴ / 24 < 1 - δ + δ² / 2 - δ³ / 6 ≤ e^{-δ}` with
`δ = 21 / 3125`.

## Main results

* `CollatzPosDens.chPairFactor_three_lt_exp`: `Fp(j, s, 3) < exp(-21 / 3125)` whenever
  `|ϑ_{n,ξ}(j, s + 3)| > 8 / 217`.

## Implementation notes

No lower bound on `j` is assumed: the index `j` is a natural number and the formula for the
pair factor holds for every `j`, including `j = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The pair factor with `b = 3` is `cos (π |ϑ_{n,ξ}(j, s + 3)|)`. -/
private theorem chPairFactor_three_eq_cos (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) :
    chPairFactor n ξ j s 3 = Real.cos (π * |bkTheta n ξ ((j : ℤ), s + 3)|) := by
  rw [chPairFactor_eq_norm_sum_exp_bkTheta n ξ j s (by norm_num : (2 : ℤ) ≤ 3)]
  set θ := bkTheta n ξ ((j : ℤ), s + 3)
  have hI : Finset.Icc 1 ((3 : ℤ).toNat - 1) = {1, 2} := by decide
  rw [hI, Finset.sum_pair (by norm_num)]
  set φ := π * θ
  have hkey : Complex.exp (-2 * π * I * ((2 : ℂ) ^ (1 - 1) - 1) * (θ : ℂ)) +
      Complex.exp (-2 * π * I * ((2 : ℂ) ^ (2 - 1) - 1) * (θ : ℂ)) =
      Complex.exp (-(φ * I)) * (2 * (Real.cos φ : ℂ)) := by
    have h1 : Complex.exp (-(φ * I)) * Complex.exp (φ * I) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have harg : -2 * π * I * ((2 : ℂ) ^ (2 - 1) - 1) * (θ : ℂ) = -(φ * I) + -(φ * I) := by
      simp only [φ]; push_cast; ring
    rw [harg, ofReal_cos, Complex.cos, Complex.exp_add, neg_mul (φ : ℂ) I]
    norm_num
    linear_combination (-1 : ℂ) * h1
  have hn : ‖Complex.exp (-(φ * I))‖ = 1 := by
    rw [← neg_mul, ← ofReal_neg, norm_exp_ofReal_mul_I]
  have hθ : |θ| ≤ 1 / 2 := abs_bkTheta_le n ξ _
  have hcos : Real.cos φ = Real.cos (π * |θ|) := by
    rcases abs_cases θ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cos_neg]
  have hnn : 0 ≤ Real.cos (π * |θ|) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [pi_pos, abs_nonneg θ]
  rw [hkey, norm_mul, hn, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hcos,
    abs_of_nonneg hnn]
  norm_num
  ring

/-- **Cancellation in a pair of white letters.** If `|ϑ_{n,ξ}(j, s + 3)| > 8 / 217`, then
`Fp(j, s, 3) < exp(-21 / 3125)`. -/
@[collatz_pos_dens "lem_ch_white_cancel"]
theorem chPairFactor_three_lt_exp {n : ℕ} {ξ : ResidueGroup n} {j : ℕ} {s : ℤ}
    (h : 8 / 217 < |bkTheta n ξ ((j : ℤ), s + 3)|) :
    chPairFactor n ξ j s 3 < Real.exp (-(21 / 3125)) := by
  rw [chPairFactor_three_eq_cos]
  set τ := |bkTheta n ξ ((j : ℤ), s + 3)|
  have hτ : τ ≤ 1 / 2 := abs_bkTheta_le n ξ _
  obtain ⟨hv0, hv1⟩ := chV0_pos_lt
  have hlt : Real.cos (π * τ) < Real.cos (chV0 : ℝ) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hv0.le (by nlinarith [pi_pos])
      (by nlinarith [pi_pos])
  have hq := cos_le_one_sub_sq_div_two_add_pow_four_div (chV0 : ℝ)
  have hr := ch_raw3_numeric_real
  have he := cubic_le_exp_neg (t := 21 / 3125) (by norm_num)
  linarith

end CollatzPosDens
