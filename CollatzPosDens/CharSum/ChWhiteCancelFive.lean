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
public import CollatzPosDens.CharSum.ChFiber5Numeric
public import CollatzPosDens.CharSum.ChFpFormula
public import CollatzPosDens.CharSum.ChV0Lower

/-!
# Cancellation at a white closing letter `5`

Fix `n : ℕ` and `ξ : ResidueGroup n`. If the angle `ϑ = ϑ_{n,ξ}(j, s + 5)` satisfies
`|ϑ| > 8 / 217`, then the pair factor with `b = 5` is small: `Fp(j, s, 5) < exp(-21 / 500)`.

With `τ = |ϑ|` and `E = e^{-2πiϑ}`, the formula for the pair factor (exponents `0, 1, 3, 7`) and
the triangle inequality give
`Fp(j, s, 5) = ¼ |1 + E + E³ + E⁷| ≤ ¼ (|1 + E| + |1 + E⁴|) = ½ (|cos (πτ)| + |cos (4πτ)|)`.
With the rational angle `v∘ = 6283 / 54250`, which satisfies `0 < v∘ < 8π / 217`, one then bounds
the right side by
`M = max (1 - (4v∘)² / 4 + (4v∘)⁴ / 48, 3 / 4, 187 / 200)` in three cases:
* `τ ≤ 1 / 8`: then `0 < 4v∘ < 4πτ ≤ π / 2`, so `0 ≤ cos (4πτ) < cos (4v∘)`, and the quartic
  Taylor bound for the cosine applies;
* `1 / 8 < τ < 1 / 6`: then `4πτ ∈ (π / 2, 2π / 3)`, so `|cos (4πτ)| < 1 / 2`;
* `1 / 6 ≤ τ ≤ 1 / 2`: then `0 ≤ cos (πτ) ≤ cos (π / 6) = √3 / 2 < 87 / 100`.
Finally `M < 1 - 21 / 500 ≤ e^{-21/500}`.

## Main results

* `CollatzPosDens.chPairFactor_five_lt_exp`: `Fp(j, s, 5) < exp(-21 / 500)` whenever
  `|ϑ_{n,ξ}(j, s + 5)| > 8 / 217`.
* `CollatzPosDens.chPairFactor_five_le_cos`:
  `Fp(j, s, 5) ≤ ½ (|cos (π ϑ)| + |cos (4π ϑ)|)` with `ϑ = ϑ_{n,ξ}(j, s + 5)`.

## Implementation notes

The hypothesis `j ≥ 1` of [mazur2026] is not needed: the formula for the pair factor holds for
every natural number `j`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- `‖1 + e^{-2iφ}‖ = 2 |cos φ|` for real `φ`. -/
private theorem norm_one_add_exp_neg_two_mul (φ : ℝ) :
    ‖1 + exp (-(φ * I) + -(φ * I))‖ = 2 * |Real.cos φ| := by
  have hkey : 1 + exp (-(φ * I) + -(φ * I)) = exp (-(φ * I)) * (2 * (Real.cos φ : ℂ)) := by
    have h1 : exp (-(φ * I)) * exp (φ * I) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    rw [ofReal_cos, Complex.cos, Complex.exp_add, neg_mul (φ : ℂ) I]
    linear_combination (-1 : ℂ) * h1
  have hn : ‖exp (-(φ * I))‖ = 1 := by
    rw [← neg_mul, ← ofReal_neg, norm_exp_ofReal_mul_I]
  rw [hkey, norm_mul, hn, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- The pair factor with `b = 5` is at most `½ (|cos (π ϑ)| + |cos (4π ϑ)|)`, where
`ϑ = ϑ_{n,ξ}(j, s + 5)`. -/
theorem chPairFactor_five_le_cos (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) :
    chPairFactor n ξ j s 5 ≤
      (|Real.cos (π * bkTheta n ξ ((j : ℤ), s + 5))| +
        |Real.cos (4 * (π * bkTheta n ξ ((j : ℤ), s + 5)))|) / 2 := by
  rw [chPairFactor_eq_norm_sum_exp_bkTheta n ξ j s (by norm_num : (2 : ℤ) ≤ 5)]
  set θ := bkTheta n ξ ((j : ℤ), s + 5)
  rw [show Finset.Icc 1 ((5 : ℤ).toNat - 1) = {1, 2, 3, 4} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  set φ := π * θ
  have hsum : Complex.exp (-2 * π * I * ((2 : ℂ) ^ (1 - 1) - 1) * (θ : ℂ)) +
      (Complex.exp (-2 * π * I * ((2 : ℂ) ^ (2 - 1) - 1) * (θ : ℂ)) +
      (Complex.exp (-2 * π * I * ((2 : ℂ) ^ (3 - 1) - 1) * (θ : ℂ)) +
        Complex.exp (-2 * π * I * ((2 : ℂ) ^ (4 - 1) - 1) * (θ : ℂ)))) =
      (1 + exp (-(φ * I) + -(φ * I))) +
        exp (((-(6 * φ) : ℝ) : ℂ) * I) *
          (1 + exp (-(((4 * φ : ℝ) : ℂ) * I) + -(((4 * φ : ℝ) : ℂ) * I))) := by
    rw [mul_add, ← Complex.exp_add]
    simp only [φ]
    push_cast
    norm_num
    ring_nf
  rw [hsum]
  have htri := norm_add_le (1 + exp (-(φ * I) + -(φ * I)))
    (exp (((-(6 * φ) : ℝ) : ℂ) * I) *
      (1 + exp (-(((4 * φ : ℝ) : ℂ) * I) + -(((4 * φ : ℝ) : ℂ) * I))))
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_one_add_exp_neg_two_mul,
    norm_one_add_exp_neg_two_mul] at htri
  rw [show (1 : ℝ) / (((5 : ℤ) : ℝ) - 1) = 1 / 4 by norm_num]
  linarith

/-- For `8 / 217 < τ ≤ 1 / 2`, `½ (|cos (πτ)| + |cos (4πτ)|) < 1 - 21 / 500`. -/
theorem abs_cos_add_abs_cos_four_lt {τ : ℝ} (h : 8 / 217 < τ) (hτ : τ ≤ 1 / 2) :
    (|Real.cos (π * τ)| + |Real.cos (4 * (π * τ))|) / 2 < 1 - 21 / 500 := by
  have hc1 := Real.abs_cos_le_one (π * τ)
  have hc4 := Real.abs_cos_le_one (4 * (π * τ))
  have hpi := pi_pos
  have hq : (1 - (4 * (chV0 : ℝ)) ^ 2 / 4 + (4 * (chV0 : ℝ)) ^ 4 / 48) < 1 - 21 / 500 := by
    have := (Rat.cast_lt (K := ℝ)).2 ((le_max_left _ _).trans_lt ch_fiber5_numeric)
    push_cast at this
    exact this
  rcases le_or_gt τ (1 / 8) with h1 | h1
  · obtain ⟨hv0, hv1⟩ := chV0_pos_lt
    have hnn : 0 ≤ Real.cos (4 * (π * τ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
    have hlt : Real.cos (4 * (π * τ)) < Real.cos (4 * (chV0 : ℝ)) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by nlinarith)
        (by nlinarith)
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
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) (by nlinarith)
    have hs : Real.sqrt 3 < 87 / 50 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    rw [Real.cos_pi_div_six] at hle
    rw [abs_of_nonneg hnn]
    linarith

/-- **Cancellation at a white closing letter `5`.** If `|ϑ_{n,ξ}(j, s + 5)| > 8 / 217`, then
`Fp(j, s, 5) < exp(-21 / 500)`. -/
@[collatz_pos_dens "lem_ch_white_cancel_five"]
theorem chPairFactor_five_lt_exp {n : ℕ} {ξ : ResidueGroup n} {j : ℕ} {s : ℤ}
    (h : 8 / 217 < |bkTheta n ξ ((j : ℤ), s + 5)|) :
    chPairFactor n ξ j s 5 < Real.exp (-(21 / 500)) := by
  have hF := chPairFactor_five_le_cos n ξ j s
  set θ := bkTheta n ξ ((j : ℤ), s + 5)
  have e1 : Real.cos (π * θ) = Real.cos (π * |θ|) := by
    rw [← Real.cos_abs (π * θ), abs_mul, abs_of_pos pi_pos]
  have e4 : Real.cos (4 * (π * θ)) = Real.cos (4 * (π * |θ|)) := by
    rw [← Real.cos_abs (4 * (π * θ)), abs_mul, abs_mul, abs_of_pos pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [e1, e4] at hF
  linarith [abs_cos_add_abs_cos_four_lt h (abs_bkTheta_le n ξ _),
    Real.add_one_le_exp (-(21 / 500 : ℝ))]

end CollatzPosDens
