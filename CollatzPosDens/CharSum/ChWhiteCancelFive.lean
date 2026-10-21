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
public import CollatzPosDens.CharSum.ChCosQuartic
public import CollatzPosDens.CharSum.ChFiber5Numeric
public import CollatzPosDens.CharSum.ChV0Lower
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.S02Z

/-!
# Cancellation at a white closing letter `5`

Fix `n : ℕ` and `ξ ∈ G_n`. If the angle `ϑ = ϑ_{n,ξ}(p)` of a point `p` satisfies `|ϑ| > ε_*`,
then the raw factor with `c = 5` is small: `φ_5(p) < exp(-z_*)`.

With `τ = |ϑ|` and `E = e^{2πiϑ}`, the packet function (exponents `0, 1, 3, 7`) and the triangle
inequality give
`φ_5(p) = ¼ |1 + E + E³ + E⁷| ≤ ¼ (|1 + E| + |1 + E⁴|) = ½ (|cos (πτ)| + |cos (4πτ)|)`.
With `v∘ = chV0`, the rational point with `0 < v∘ < π ε_*`, one bounds the right side by
`M = max (1 - (4v∘)² / 4 + (4v∘)⁴ / 48, 3 / 4, 187 / 200)` in three cases:
* `τ ≤ 1 / 8`: then `0 < 4v∘ < 4πτ ≤ π / 2`, so `0 ≤ cos (4πτ) < cos (4v∘)`, and the quartic
  Taylor bound for the cosine applies;
* `1 / 8 < τ < 1 / 6`: then `4πτ ∈ (π / 2, 2π / 3)`, so `|cos (4πτ)| < 1 / 2`;
* `1 / 6 ≤ τ ≤ 1 / 2`: then `0 ≤ cos (πτ) ≤ cos (π / 6) = √3 / 2 < 87 / 100`.
Finally `M < 1 - z_* ≤ e^{-z_*}`.

## Main results

* `CollatzPosDens.chPairFactor_five_lt_exp`: `φ_5(p) < exp(-z_*)` whenever
  `|ϑ_{n,ξ}(p)| > ε_*`.
* `CollatzPosDens.chPacketFn_four_le_cos`:
  `Φ_4(θ) ≤ ½ (|cos (π θ)| + |cos (4π θ)|)` for every real `θ`.
* `CollatzPosDens.abs_cos_add_abs_cos_four_mul_div_two_lt`: for `ε_* < τ ≤ 1 / 2`,
  `½ (|cos (πτ)| + |cos (4πτ)|) < 1 - z_*`.

## Implementation notes

The point `p` ranges over all of `ℤ × ℤ`, not only over `𝒫`, since the angle and the raw factor
are defined there; the statement on `𝒫` is a special case.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- `‖1 + e^{2iφ}‖ = 2 |cos φ|` for real `φ`. -/
private theorem norm_one_add_exp_two_mul (φ : ℝ) :
    ‖1 + exp (φ * I + φ * I)‖ = 2 * |Real.cos φ| := by
  have hkey : 1 + exp (φ * I + φ * I) = exp (φ * I) * (2 * (Real.cos φ : ℂ)) := by
    have h1 : exp (-(φ * I)) * exp (φ * I) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    rw [ofReal_cos, Complex.cos, Complex.exp_add, neg_mul (φ : ℂ) I]
    linear_combination (-1 : ℂ) * h1
  rw [hkey, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  norm_num

/-- The packet function of length `4` is at most `½ (|cos (π θ)| + |cos (4π θ)|)`. -/
theorem chPacketFn_four_le_cos (θ : ℝ) :
    chPacketFn 4 θ ≤ (|Real.cos (π * θ)| + |Real.cos (4 * (π * θ))|) / 2 := by
  rw [chPacketFn_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  set φ := π * θ
  have hsum : Complex.exp (2 * π * I * ((((2 : ℝ) ^ 0 - 1) * θ : ℝ) : ℂ)) +
      Complex.exp (2 * π * I * ((((2 : ℝ) ^ 1 - 1) * θ : ℝ) : ℂ)) +
      Complex.exp (2 * π * I * ((((2 : ℝ) ^ 2 - 1) * θ : ℝ) : ℂ)) +
      Complex.exp (2 * π * I * ((((2 : ℝ) ^ 3 - 1) * θ : ℝ) : ℂ)) =
      (1 + exp (φ * I + φ * I)) +
        exp (((6 * φ : ℝ) : ℂ) * I) *
          (1 + exp (((4 * φ : ℝ) : ℂ) * I + ((4 * φ : ℝ) : ℂ) * I)) := by
    rw [mul_add, ← Complex.exp_add]
    simp only [φ]
    push_cast
    norm_num
    ring_nf
  rw [hsum]
  have htri := norm_add_le (1 + exp (φ * I + φ * I))
    (exp (((6 * φ : ℝ) : ℂ) * I) *
      (1 + exp (((4 * φ : ℝ) : ℂ) * I + ((4 * φ : ℝ) : ℂ) * I)))
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_one_add_exp_two_mul,
    norm_one_add_exp_two_mul] at htri
  rw [show (1 : ℝ) / ((4 : ℕ) : ℝ) = 1 / 4 by norm_num]
  linarith

/-- For `ε_* < τ ≤ 1 / 2`, `½ (|cos (πτ)| + |cos (4πτ)|) < 1 - z_*`. -/
theorem abs_cos_add_abs_cos_four_mul_div_two_lt {τ : ℝ} (h : (epsStar : ℝ) < τ)
    (hτ : τ ≤ 1 / 2) :
    (|Real.cos (π * τ)| + |Real.cos (4 * (π * τ))|) / 2 < 1 - (zStar : ℝ) := by
  have hc1 := Real.abs_cos_le_one (π * τ)
  have hc4 := Real.abs_cos_le_one (4 * (π * τ))
  have hpi := pi_pos
  have heps : (0 : ℝ) < epsStar := by exact_mod_cast epsStar_pos
  have hnum := ch_fiber5_numeric
  have hq : (1 - (4 * (chV0 : ℝ)) ^ 2 / 4 + (4 * (chV0 : ℝ)) ^ 4 / 48) < 1 - (zStar : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 ((le_max_left _ _).trans_lt hnum)
    rw [zStar_cast]
    push_cast at this
    exact this
  have h34 : (3 / 4 : ℝ) < 1 - (zStar : ℝ) := by rw [zStar_cast]; norm_num
  have h187 : (187 / 200 : ℝ) < 1 - (zStar : ℝ) := by rw [zStar_cast]; norm_num
  rcases le_or_gt τ (1 / 8) with h1 | h1
  · obtain ⟨hv0, hv1⟩ := chV0_pos_lt
    have hv2 : (chV0 : ℝ) < π * τ := hv1.trans (mul_lt_mul_of_pos_left h hpi)
    have hnn : 0 ≤ Real.cos (4 * (π * τ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
    have hlt : Real.cos (4 * (π * τ)) < Real.cos (4 * (chV0 : ℝ)) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by nlinarith) (by nlinarith)
    have hquart := cos_le_one_sub_sq_div_two_add_pow_four_div (4 * (chV0 : ℝ))
    rw [abs_of_nonneg hnn]
    linarith
  rcases lt_or_ge τ (1 / 6) with h2 | h2
  · have hneg : Real.cos (4 * (π * τ)) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith) (by nlinarith)
    have h23 : Real.cos (2 * π / 3) < Real.cos (4 * (π * τ)) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by nlinarith) (by nlinarith) (by nlinarith)
    have hval : Real.cos (2 * π / 3) = -(1 / 2) := by
      rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [abs_of_neg hneg]
    linarith
  · have hnn : 0 ≤ Real.cos (π * τ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
    have hle : Real.cos (π * τ) ≤ Real.cos (π / 6) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by nlinarith) (by nlinarith)
    have hs : Real.sqrt 3 < 87 / 50 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    rw [Real.cos_pi_div_six] at hle
    rw [abs_of_nonneg hnn]
    linarith

/-- **Cancellation at a white closing letter `5`.** If `|ϑ_{n,ξ}(p)| > ε_*`, then
`φ_5(p) < exp(-z_*)`. -/
@[collatz_pos_dens "lem_ch_white_cancel_five"]
theorem chPairFactor_five_lt_exp {n : ℕ} {ξ : ResidueGroup n} {p : ℤ × ℤ}
    (h : (epsStar : ℝ) < |bkTheta n ξ p|) :
    chRawFactor n ξ 5 p < Real.exp (-(zStar : ℝ)) := by
  rw [chRawFactor_of_two_le n ξ (by norm_num), show ((5 : ℤ) - 1).toNat = 4 by decide]
  have hF := chPacketFn_four_le_cos (bkTheta n ξ p)
  set θ := bkTheta n ξ p
  have e1 : Real.cos (π * θ) = Real.cos (π * |θ|) := by
    rw [← Real.cos_abs (π * θ), abs_mul, abs_of_pos pi_pos]
  have e4 : Real.cos (4 * (π * θ)) = Real.cos (4 * (π * |θ|)) := by
    rw [← Real.cos_abs (4 * (π * θ)), abs_mul, abs_mul, abs_of_pos pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [e1, e4] at hF
  have hB := abs_cos_add_abs_cos_four_mul_div_two_lt h (abs_bkTheta_le n ξ _)
  linarith [Real.add_one_le_exp (-(zStar : ℝ))]

end CollatzPosDens
