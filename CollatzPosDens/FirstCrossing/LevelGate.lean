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
# The level gate `k_n ≥ 2^80000`

For every `n ≥ 6000000` the residue level satisfies `k_n ≥ 2^80000`. Indeed, since
`n ≥ 444`, the late lower bound gives `k_n ≥ 47 𝗀^n > 𝗀^n = 2^{nδ}`, where `δ = log₂ 𝗀` is the
logarithmic growth rate, and `nδ > n/70 ≥ 6000000/70 > 85714 > 80000` because `δ > 1/70`.

## Main results

* `CollatzPosDens.level_gate`: `2^80000 ≤ k_n` for all `n ≥ 6000000`.

## Implementation notes

The conclusion is stated in `ℕ`, where the level lives. The power `2^80000` is never
evaluated: the comparison is carried out in `ℝ` through `2^{nδ} = 𝗀^n` and the strict
monotonicity of `x ↦ 2^x`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Lemma.** For every `n ≥ 6000000`, `k_n ≥ 2^80000`. -/
@[collatz_pos_dens "lem_level_gate"]
theorem level_gate {n : ℕ} (hn : 6000000 ≤ n) : 2 ^ 80000 ≤ level n := by
  have h1 := level_late_lower (j := n) (by omega)
  have hn' : (6000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ := one_div_seventy_lt_logGrowthRate
  have hexp : (80000 : ℝ) < logGrowthRate * n := by nlinarith
  have h2 : (2 : ℝ) ^ (80000 : ℝ) < 2 ^ (logGrowthRate * n) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  have h3 : (2 : ℝ) ^ (logGrowthRate * n) = (growthRatio : ℝ) ^ n := by
    rw [Real.rpow_mul (by norm_num), rpow_logGrowthRate, Real.rpow_natCast]
  have hg : 0 ≤ (growthRatio : ℝ) ^ n := by
    rw [growthRatio_cast]; positivity
  have h4 : (((2 ^ 80000 : ℕ)) : ℝ) = (2 : ℝ) ^ (80000 : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    norm_num only [Nat.cast_ofNat]
  have h5 : (((2 ^ 80000 : ℕ)) : ℝ) ≤ (level n : ℝ) := by
    rw [h4]
    refine le_trans h2.le ?_
    rw [h3]
    exact le_trans (le_mul_of_one_le_left hg (by norm_num)) h1
  exact Nat.cast_le.mp h5

end CollatzPosDens
