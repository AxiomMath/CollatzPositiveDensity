/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSignedFrac
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.CharSum.ChPacketFn
public import CollatzPosDens.CharSum.ChU0
public import CollatzPosDens.CharSum.ChV0
public import CollatzPosDens.CharSum.ChExpCubic
public import CollatzPosDens.CharSum.ChFiber4Numeric
public import CollatzPosDens.CharSum.ChV0Lower
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.S02Z
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cancellation at a white closing letter `4`

Fix `n : ℕ` and `ξ ∈ G_n`. If the angle `ϑ = ϑ_{n,ξ}(p)` of a point `p` satisfies `|ϑ| > ε_*`,
then the raw factor with `c = 4` is small: `φ_4(p) < e^{-z_*}`.

By `chPacketFn` (exponents `0, 1, 3`), `φ_4(p) = |1 + E + E³| / 3` with `E = e^{2πiϑ}`.
Writing `u = sin²(πϑ)`, the multiple-angle formulas give `|1 + E + E³|² = 9 - 4R(u)` with
`R(u) = 14u - 28u² + 16u³`. Since `π|ϑ| ∈ (v∘, π/2]`, the cubic Taylor bound for the sine gives
`u > u∘`. On `[0, 1/4]` the cubic `R` is nondecreasing, and for `u > 1/4` one has
`R(u) - 7u/4 = 16u(u - 7/8)² ≥ 0`; hence `R(u) ≥ min(R(u∘), 7/16)`. The numerical inequality
`ch_fiber4_numeric_real` and the cubic lower bound `cubic_le_exp_neg` for `e^{-t}` at `t = 2z_*`
then give `9 φ_4(p)² < 9 e^{-2z_*}`.

## Main results

* `CollatzPosDens.chPairFactor_four_lt_exp_neg`: `φ_4(p) < e^{-z_*}` whenever
  `|ϑ_{n,ξ}(p)| > ε_*`.
* `CollatzPosDens.chPacketFn_three_sq_eq`: `9 Φ_3(θ)² = 9 - 4R(sin²(πθ))`.

## Implementation notes

The point `p` ranges over all of `ℤ × ℤ`, not only over `𝒫`, since the angle and the raw factor
are defined there; the statement on `𝒫` is a special case.

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

/-- The packet function of length `3` through `u = sin²(πθ)`:
`9 Φ_3(θ)² = 9 - 4(14u - 28u² + 16u³)`. -/
theorem chPacketFn_three_sq_eq (θ : ℝ) :
    9 * chPacketFn 3 θ ^ 2 =
      9 - 4 * (14 * sin (π * θ) ^ 2 - 28 * (sin (π * θ) ^ 2) ^ 2 +
        16 * (sin (π * θ) ^ 2) ^ 3) := by
  rw [chPacketFn_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hsum : Complex.exp (2 * π * Complex.I * ((((2 : ℝ) ^ 0 - 1) * θ : ℝ) : ℂ)) +
      Complex.exp (2 * π * Complex.I * ((((2 : ℝ) ^ 1 - 1) * θ : ℝ) : ℂ)) +
      Complex.exp (2 * π * Complex.I * ((((2 : ℝ) ^ 2 - 1) * θ : ℝ) : ℂ)) =
      1 + Complex.exp (↑(2 * π * θ) * Complex.I) +
        Complex.exp (↑(3 * (2 * π * θ)) * Complex.I) := by
    push_cast
    norm_num
    congr 2 <;> ring_nf
  rw [hsum, mul_pow, norm_one_add_exp_add_exp_three_sq, show 2 * π * θ / 2 = π * θ by ring]
  norm_num
  ring

/-- **Cancellation at a white closing letter `4`.** If `|ϑ_{n,ξ}(p)| > ε_*`, then
`φ_4(p) < exp(-z_*)`. -/
@[collatz_pos_dens "lem_ch_white_cancel_four"]
theorem chPairFactor_four_lt_exp_neg {n : ℕ} {ξ : ResidueGroup n} {p : ℤ × ℤ}
    (h : (epsStar : ℝ) < |bkTheta n ξ p|) :
    chRawFactor n ξ 4 p < exp (-(zStar : ℝ)) := by
  rw [chRawFactor_of_two_le n ξ (by norm_num), show ((4 : ℤ) - 1).toNat = 3 by decide]
  set θ := bkTheta n ξ p
  have hsq := chPacketFn_three_sq_eq θ
  set u := sin (π * θ) ^ 2
  have hu_abs : u = sin (π * |θ|) ^ 2 := by
    rcases abs_cases θ with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]
    · rw [h1, mul_neg, sin_neg, neg_sq]
  obtain ⟨hv0, hv1⟩ := chV0_pos_lt
  have hτ : |θ| ≤ 1 / 2 := abs_bkTheta_le n ξ _
  have hπ := pi_pos
  have hlt : (chV0 : ℝ) < π * |θ| := hv1.trans (mul_lt_mul_of_pos_left h hπ)
  have hle : π * |θ| ≤ π / 2 := by nlinarith
  have hsin : sin (chV0 : ℝ) < sin (π * |θ|) :=
    sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hle hlt
  have hcub : (chV0 : ℝ) - (chV0 : ℝ) ^ 3 / 6 ≤ sin (chV0 : ℝ) := by
    have h3 := Real.abs_sub_sin_le (chV0 : ℝ)
    rw [abs_of_pos hv0] at h3
    linarith [le_abs_self ((chV0 : ℝ) - sin (chV0 : ℝ))]
  have hcpos : (0 : ℝ) < (chV0 : ℝ) - (chV0 : ℝ) ^ 3 / 6 := by exact_mod_cast chV0_sub_cube_pos
  have hu0 : (chU0 : ℝ) < u := by
    rw [hu_abs, chU0_def]
    push_cast
    exact pow_lt_pow_left₀ (hcub.trans_lt hsin) hcpos.le two_ne_zero
  have hu0q : (chU0 : ℝ) ≤ 1 / 4 := by rw [chU0_eq]; norm_num
  have hu0n : (0 : ℝ) ≤ chU0 := by exact_mod_cast chU0_nonneg
  have hR : min (14 * (chU0 : ℝ) - 28 * (chU0 : ℝ) ^ 2 + 16 * (chU0 : ℝ) ^ 3) (7 / 16) ≤
      14 * u - 28 * u ^ 2 + 16 * u ^ 3 := by
    rcases le_or_gt u (1 / 4) with hu | hu
    · refine min_le_of_left_le ?_
      have hfac : 0 ≤ 14 - 28 * (u + chU0) + 16 * (u ^ 2 + u * chU0 + (chU0 : ℝ) ^ 2) := by
        nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 hu0.le) hfac]
    · refine min_le_of_right_le ?_
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * u) (sq_nonneg (u - 7 / 8))]
  have hnum := ch_fiber4_numeric_real
  have hexp := cubic_le_exp_neg (t := 2 * (zStar : ℝ)) (by rw [zStar_cast]; norm_num)
  have hexp2 : exp (-(2 * (zStar : ℝ))) = exp (-(zStar : ℝ)) ^ 2 := by
    rw [← exp_nat_mul]
    norm_num
  rw [zStar_cast] at hexp hexp2 ⊢
  have h9 : 9 * chPacketFn 3 θ ^ 2 < 9 * exp (-(133 / 3125 : ℝ)) ^ 2 := by
    rw [← hexp2]
    nlinarith
  exact (pow_lt_pow_iff_left₀ (chPacketFn_nonneg 3 θ) (exp_pos _).le two_ne_zero).1
    (by linarith)

end CollatzPosDens
