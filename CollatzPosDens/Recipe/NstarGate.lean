/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhDeltaBounds
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Transfer.MxGate

/-!
# The gate level lies below `2^12 𝗀^{N_*}`

The mixing gate level `n₀ = 2^80` is smaller than `2^12 𝗀^{N_*}`, where `𝗀 = 101/100` is the
physical growth ratio and `N_* = 9853` the generation threshold.

Since `δ = log₂ 𝗀 > 1/70`, `𝗀^70 = 2^{70δ} > 2`. As `N_* ≥ 70 · 140 = 9800` and `𝗀 ≥ 1`,
`𝗀^{N_*} ≥ (𝗀^70)^140 > 2^140 ≥ 2^68`, whence `2^12 𝗀^{N_*} > 2^80 = n₀`.

## Main results

* `CollatzPosDens.two_lt_growthRatio_pow_seventy`: `2 < 𝗀^70`.
* `CollatzPosDens.mxGateLevel_lt_two_pow_twelve_mul_growthRatio_pow`: `n₀ < 2^12 𝗀^{N_*}`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The seventieth power of the growth ratio exceeds two: `2 < 𝗀^70`. -/
theorem two_lt_growthRatio_pow_seventy : (2 : ℝ) < (growthRatio : ℝ) ^ 70 := by
  rw [← rpow_logGrowthRate, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h := one_div_seventy_lt_logGrowthRate
  calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
    _ < 2 ^ (logGrowthRate * ((70 : ℕ) : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by push_cast; linarith)

/-- The mixing gate level is below `2^12 𝗀^{N_*}`: `n₀ < 2^12 𝗀^{N_*}`. -/
@[collatz_pos_dens "lem_Nstar_gate"]
theorem mxGateLevel_lt_two_pow_twelve_mul_growthRatio_pow :
    (mxGateLevel : ℝ) < 2 ^ 12 * (growthRatio : ℝ) ^ generationThreshold := by
  have hg : (1 : ℝ) ≤ growthRatio := one_lt_growthRatio_cast.le
  have hpow : (2 : ℝ) ^ 68 < (growthRatio : ℝ) ^ generationThreshold :=
    calc (2 : ℝ) ^ 68 ≤ 2 ^ 140 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ < ((growthRatio : ℝ) ^ 70) ^ 140 :=
          pow_lt_pow_left₀ two_lt_growthRatio_pow_seventy (by norm_num) (by norm_num)
      _ = (growthRatio : ℝ) ^ 9800 := by rw [← pow_mul]
      _ ≤ (growthRatio : ℝ) ^ generationThreshold :=
          pow_le_pow_right₀ hg (by rw [generationThreshold_def]; norm_num)
  calc (mxGateLevel : ℝ) = 2 ^ 12 * 2 ^ 68 := by rw [mxGateLevel_def]; norm_num
    _ < 2 ^ 12 * (growthRatio : ℝ) ^ generationThreshold := by gcongr

end CollatzPosDens
