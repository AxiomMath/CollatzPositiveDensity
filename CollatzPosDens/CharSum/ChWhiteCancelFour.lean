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
public import CollatzPosDens.CharSum.ChU0
public import CollatzPosDens.CharSum.ChV0
public import CollatzPosDens.CharSum.ChExpCubic
public import CollatzPosDens.CharSum.ChFiber4Numeric
public import CollatzPosDens.CharSum.ChFpFormula
public import CollatzPosDens.CharSum.ChV0Lower
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cancellation at a white closing letter `4`

Fix `n : ℕ` and `ξ ∈ G_n`. If the angle `ϑ = ϑ_{n,ξ}(j, s + 4)` satisfies `|ϑ| > 8 / 217`, then
the pair factor satisfies `Fp(j, s, 4) < e^{-21/500}`.

By the formula for the pair factor through the angle, `Fp(j, s, 4) = |1 + E + E³| / 3` with
`E = e^{-2πiϑ}`. Writing `u = sin²(πϑ)`, the multiple-angle formulas give
`|1 + E + E³|² = 9 - 4R(u)` with `R(u) = 14u - 28u² + 16u³`. With the rational angle
`v∘ = 6283 / 54250` (`CollatzPosDens.chV0`) and `u∘ = (v∘ - v∘³/6)²` (`CollatzPosDens.chU0`), one
has `π|ϑ| ∈ (v∘, π/2]`, so the cubic Taylor bound for the sine gives `u > u∘`. On `[0, 1/4]` the
cubic `R` is nondecreasing, and for `u > 1/4` one has `R(u) - 7u/4 = 16u(u - 7/8)² ≥ 0`; hence
`R(u) ≥ min(R(u∘), 7/16)`. The numerical inequality for the letter `4` and the cubic lower bound
for `e^{-t}` at `t = 2 · 21/500` then give `9 Fp(j, s, 4)² < 9 e^{-2 · 21/500}`.

## Main results

* `CollatzPosDens.chPairFactor_four_lt_exp_neg`: `Fp(j, s, 4) < e^{-21/500}` whenever
  `|ϑ_{n,ξ}(j, s + 4)| > 8 / 217`.
* `CollatzPosDens.chPairFactor_four_sq_eq`: `9 Fp(j, s, 4)² = 9 - 4R(sin²(πϑ))`.

## Implementation notes

The hypothesis `j ≥ 1` of [mazur2026] is not needed, since the formula for the pair factor through
the angle holds for every natural number `j`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- `|1 + e^{ia} + e^{3ia}|² = 9 - 4R(sin²(a/2))` with `R(u) = 14u - 28u² + 16u³`. -/
private lemma norm_one_add_exp_add_exp_three_sq (a : ℝ) :
    ‖(1 : ℂ) + Complex.exp (↑a * Complex.I) + Complex.exp (↑(3 * a) * Complex.I)‖ ^ 2 =
      9 - 4 * (14 * sin (a / 2) ^ 2 - 28 * (sin (a / 2) ^ 2) ^ 2 +
        16 * (sin (a / 2) ^ 2) ^ 3) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hc : cos a = 1 - 2 * sin (a / 2) ^ 2 := by
    have := cos_sq (a / 2)
    rw [show 2 * (a / 2) = a by ring] at this
    have := sin_sq_add_cos_sq (a / 2)
    linarith
  have hp := sin_sq_add_cos_sq a
  rw [cos_three_mul, sin_three_mul]
  set C := cos a
  set S := sin a
  have hu : sin (a / 2) ^ 2 = (1 - C) / 2 := by linarith
  rw [hu]
  linear_combination
    16 * (1 - 2 * (S ^ 2 + (1 - C ^ 2)) + S ^ 4 + S ^ 2 * (1 - C ^ 2) + (1 - C ^ 2) ^ 2) * hp

/-- The pair factor at the closing letter `4` through `u = sin²(πϑ)`:
`9 Fp(j, s, 4)² = 9 - 4(14u - 28u² + 16u³)` with `ϑ = ϑ_{n,ξ}(j, s + 4)`. -/
theorem chPairFactor_four_sq_eq (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) :
    9 * chPairFactor n ξ j s 4 ^ 2 =
      9 - 4 * (14 * sin (π * bkTheta n ξ ((j : ℤ), s + 4)) ^ 2 -
        28 * (sin (π * bkTheta n ξ ((j : ℤ), s + 4)) ^ 2) ^ 2 +
        16 * (sin (π * bkTheta n ξ ((j : ℤ), s + 4)) ^ 2) ^ 3) := by
  set θ := bkTheta n ξ ((j : ℤ), s + 4)
  rw [chPairFactor_eq_norm_sum_exp_bkTheta n ξ j s (by norm_num : (2 : ℤ) ≤ 4)]
  have hI : Finset.Icc 1 ((4 : ℤ).toNat - 1) = {1, 2, 3} := by decide
  have hsum : ∑ t ∈ Finset.Icc 1 ((4 : ℤ).toNat - 1),
      Complex.exp (-2 * π * Complex.I * ((2 : ℂ) ^ (t - 1) - 1) * (θ : ℂ)) =
      1 + Complex.exp (↑(-2 * π * θ) * Complex.I) +
        Complex.exp (↑(3 * (-2 * π * θ)) * Complex.I) := by
    rw [hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    norm_num
    rw [add_assoc]
    congr 3 <;> ring
  rw [hsum, mul_pow, norm_one_add_exp_add_exp_three_sq,
    show -2 * π * θ / 2 = -(π * θ) by ring, sin_neg, neg_sq]
  ring

/-- For `u₀ < u`, the cubic `14 u - 28 u ^ 2 + 16 u ^ 3` is bounded below by
`min (14 u₀ - 28 u₀ ^ 2 + 16 u₀ ^ 3) (7 / 16)`. -/
theorem min_cubic_le_cubic_of_lt {u₀ u : ℝ} (hu₀ : u₀ < u) :
    min (14 * u₀ - 28 * u₀ ^ 2 + 16 * u₀ ^ 3) (7 / 16) ≤ 14 * u - 28 * u ^ 2 + 16 * u ^ 3 := by
  rcases le_or_gt u (1 / 4) with hu | hu
  · refine min_le_of_left_le ?_
    have hfac : 0 ≤ 14 - 28 * (u + u₀) + 16 * (u ^ 2 + u * u₀ + u₀ ^ 2) := by
      nlinarith [sq_nonneg (u + u₀), sq_nonneg u, sq_nonneg u₀]
    nlinarith [mul_nonneg (sub_nonneg.2 hu₀.le) hfac]
  · refine min_le_of_right_le ?_
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * u) (sq_nonneg (u - 7 / 8))]

/-- **Cancellation at a white closing letter `4`.** If `|ϑ_{n,ξ}(j, s + 4)| > 8 / 217`, then
`Fp(j, s, 4) < e^{-21/500}`. -/
@[collatz_pos_dens "lem_ch_white_cancel_four"]
theorem chPairFactor_four_lt_exp_neg (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ)
    (h : 8 / 217 < |bkTheta n ξ ((j : ℤ), s + 4)|) :
    chPairFactor n ξ j s 4 < exp (-(21 / 500)) := by
  set θ := bkTheta n ξ ((j : ℤ), s + 4)
  have hsq := chPairFactor_four_sq_eq n ξ j s
  set u := sin (π * θ) ^ 2
  have hu_abs : u = sin (π * |θ|) ^ 2 := by
    rcases abs_cases θ with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]
    · rw [h1, mul_neg, sin_neg, neg_sq]
  obtain ⟨hv0, hv1⟩ := chV0_pos_lt
  have hτ : |θ| ≤ 1 / 2 := abs_bkTheta_le n ξ _
  have hπ := pi_pos
  have hlt : (chV0 : ℝ) < π * |θ| := by linarith [mul_lt_mul_of_pos_left h hπ]
  have hle : π * |θ| ≤ π / 2 := by nlinarith
  have hsin : sin (chV0 : ℝ) < sin (π * |θ|) :=
    sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hle hlt
  have hcub : (chV0 : ℝ) - (chV0 : ℝ) ^ 3 / 6 ≤ sin (chV0 : ℝ) := sin_ge_sub_cube hv0.le
  have hcpos : (0 : ℝ) < (chV0 : ℝ) - (chV0 : ℝ) ^ 3 / 6 := by
    exact_mod_cast chV0_sub_cube_pos
  have hu0 : (chU0 : ℝ) < u := by
    rw [hu_abs, chU0_def]
    push_cast
    exact pow_lt_pow_left₀ (hcub.trans_lt hsin) hcpos.le two_ne_zero
  have hu0q : (chU0 : ℝ) ≤ 1 / 4 := by rw [chU0_eq]; norm_num
  have hR := min_cubic_le_cubic_of_lt hu0
  have hnum := ch_fiber4_numeric_real
  have hexp := cubic_le_exp_neg (t := 2 * (21 / 500)) (by norm_num)
  have hexp2 : exp (-(2 * (21 / 500) : ℝ)) = exp (-(21 / 500)) ^ 2 := by
    rw [← exp_nat_mul]
    norm_num
  have h9 : 9 * chPairFactor n ξ j s 4 ^ 2 < 9 * exp (-(21 / 500)) ^ 2 := by
    rw [← hexp2]
    nlinarith
  exact (pow_lt_pow_iff_left₀ (chPairFactor_nonneg n ξ j s 4) (exp_pos _).le two_ne_zero).1
    (by linarith)

end CollatzPosDens
