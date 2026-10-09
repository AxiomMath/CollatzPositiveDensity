/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.PhDelta
public import CollatzPosDens.FirstCrossing.LevelLateLower
public import CollatzPosDens.FirstCrossing.PhDeltaBounds

/-!
# A lower bound `2^131072 ≤ level n` for large `n`

For every `n ≥ 9200000` the residue level satisfies `2^131072 ≤ level n`. Indeed, since
`n ≥ 444`, the bound `level_late_lower` gives `level n ≥ 47 g^n > g^n = 2^{nδ}`, where
`g = growthRatio` and `δ = logGrowthRate = log₂ g`, and `nδ > n/70 ≥ 9200000/70 > 131072`
because `δ > 1/70` (`one_div_seventy_lt_logGrowthRate`).

## Main results

* `CollatzPosDens.level_gate`: `2^131072 ≤ level n` for all `n ≥ 9200000`.

## Implementation notes

The conclusion is stated in `ℕ`, where `level` takes values. The power `2^131072` is never
evaluated: the comparison is carried out in `ℝ` through `2^{nδ} = g^n` and the strict
monotonicity of `x ↦ 2^x`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `n ≥ 9200000`, the residue level satisfies `2^131072 ≤ level n`. -/
@[collatz_pos_dens "lem_level_gate"]
theorem level_gate {n : ℕ} (hn : 9200000 ≤ n) : 2 ^ 131072 ≤ level n := by
  have h1 := level_late_lower (j := n) (by omega)
  have hn' : (9200000 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ := one_div_seventy_lt_logGrowthRate
  have hexp : (131072 : ℝ) < logGrowthRate * n := by nlinarith
  have h2 : (2 : ℝ) ^ (131072 : ℝ) < 2 ^ (logGrowthRate * n) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  have h3 : (2 : ℝ) ^ (logGrowthRate * n) = (growthRatio : ℝ) ^ n := by
    rw [Real.rpow_mul (by norm_num), rpow_logGrowthRate, Real.rpow_natCast]
  have hg : 0 ≤ (growthRatio : ℝ) ^ n := by
    rw [growthRatio_cast]; positivity
  have h4 : (((2 ^ 131072 : ℕ)) : ℝ) = (2 : ℝ) ^ (131072 : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    norm_num only [Nat.cast_ofNat]
  have h5 : (((2 ^ 131072 : ℕ)) : ℝ) ≤ (level n : ℝ) := by
    rw [h4]
    refine le_trans h2.le ?_
    rw [h3]
    exact le_trans (le_mul_of_one_le_left hg (by norm_num)) h1
  exact Nat.cast_le.mp h5

end CollatzPosDens
