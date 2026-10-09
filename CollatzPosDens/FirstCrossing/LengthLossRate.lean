/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Recipe.Varsigma
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesGrowth

/-!
# Decay of the length loss

Write `b_n = scale n`, `ς = deficitRate` and `𝗀 = growthRatio`. The bound `2^{114} b_n^{-6}`
decays at the rate `ς`:
$$2^{114} b_n^{-6} \le 2^{95} \varsigma^n \qquad (n \in \mathbb{N}).$$
By the geometric growth of the scales, `b_n ≥ 9 𝗀^n`, so `b_n^{-6} ≤ 9^{-6} (𝗀^{-6})^n`.
Since `ς^8 = 𝗀^{-9} ≥ 𝗀^{-48} = (𝗀^{-6})^8`, we have `𝗀^{-6} ≤ ς`, and `2^{114} 9^{-6} ≤ 2^{95}`
because `9^6 = 531441 > 2^{19}`.

## Main results

* `CollatzPosDens.lengthLossRate_le`: `2^{114} b_n^{-6} ≤ 2^{95} ς^n`.
-/

@[expose] public section

namespace CollatzPosDens

/-- `𝗀^{-6} ≤ ς`, compared through eighth powers: `ς^8 = 𝗀^{-9} ≥ 𝗀^{-48}`. -/
private theorem growthRatio_inv_pow_six_le_deficitRate :
    ((growthRatio : ℝ)⁻¹) ^ 6 ≤ deficitRate := by
  refine le_of_pow_le_pow_left₀ (n := 8) (by norm_num) deficitRate_nonneg ?_
  rw [deficitRate_pow_eight, growthRatio_cast]
  norm_num

/-- For every `n ∈ ℕ`, `2^{114} b_n^{-6} ≤ 2^{95} ς^n`, where `b_n = scale n` and
`ς = deficitRate`. -/
@[collatz_pos_dens "lem_length_loss_rate"]
theorem lengthLossRate_le (n : ℕ) :
    (2 : ℝ) ^ 114 * (scale n : ℝ) ^ (-6 : ℤ) ≤ 2 ^ 95 * deficitRate ^ n := by
  have hg := growthRatio_cast_pos
  have hgrow : (growthRatio : ℝ) ^ n * 9 ≤ scale n := by
    simpa using scale_add_ge_growthRatio_pow_mul 0 n
  have hpos : 0 < (growthRatio : ℝ) ^ n * 9 := by positivity
  have h1 : (scale n : ℝ) ^ (-6 : ℤ) ≤ (((growthRatio : ℝ) ^ n * 9) ^ 6)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hgrow 6)
  have h2 : (((growthRatio : ℝ) ^ n * 9) ^ 6)⁻¹ = (((growthRatio : ℝ)⁻¹) ^ 6) ^ n / 9 ^ 6 := by
    rw [← pow_mul, mul_comm 6 n, pow_mul, inv_pow, mul_pow, mul_inv, div_eq_mul_inv, inv_pow]
  have h3 : (((growthRatio : ℝ)⁻¹) ^ 6) ^ n ≤ deficitRate ^ n :=
    pow_le_pow_left₀ (by positivity) growthRatio_inv_pow_six_le_deficitRate n
  rw [h2] at h1
  have hd : 0 ≤ deficitRate ^ n := pow_nonneg deficitRate_nonneg n
  calc (2 : ℝ) ^ 114 * (scale n : ℝ) ^ (-6 : ℤ)
      ≤ 2 ^ 114 * ((((growthRatio : ℝ)⁻¹) ^ 6) ^ n / 9 ^ 6) := by gcongr
    _ ≤ 2 ^ 114 * (deficitRate ^ n / 9 ^ 6) := by gcongr
    _ = (2 ^ 114 / 9 ^ 6) * deficitRate ^ n := by ring
    _ ≤ 2 ^ 95 * deficitRate ^ n := by gcongr; norm_num

end CollatzPosDens
