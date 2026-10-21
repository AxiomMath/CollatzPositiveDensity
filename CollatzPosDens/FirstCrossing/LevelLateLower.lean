/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.ScalesLateLower
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.NstarGate
public import CollatzPosDens.Transfer.MxGate
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# A lower bound for the late levels

For every `j ≥ N_*` (the generation threshold `N_* = 9853`) the residue level
`k_j = ⌊b_j / 4⌋` satisfies
$$k_j \ge \max\bigl(n_0,\, 2^{12}\,\mathsf g^{\,j}\bigr),$$
where `n_0 = 2^80` is the mixing gate level and `𝗀 = 101/100` is the physical growth ratio.
Indeed, for every `j`, `k_j > b_j/4 - 1 ≥ 4136 𝗀^j - 1` by the lower bound `b_j ≥ 16544 𝗀^j`
on the scales, and `4136 𝗀^j - 1 ≥ 2^{12} 𝗀^j` because `𝗀^j ≥ 1`. For `j ≥ N_*` moreover
`2^{12} 𝗀^j ≥ 2^{12} 𝗀^{N_*} > n_0`, by the gate comparison
`mxGateLevel_lt_two_pow_twelve_mul_growthRatio_pow`.

## Main results

* `CollatzPosDens.two_pow_twelve_mul_growthRatio_pow_le_level`: `2^12 𝗀^j ≤ k_j` for all `j`.
* `CollatzPosDens.level_late_lower`: `max n_0 (2^12 𝗀^j) ≤ k_j` for all `j ≥ N_*`.

## Implementation notes

The inequalities are stated in `ℝ`, with the rational ratio `𝗀` and the natural-number level
cast to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `j ∈ ℕ`, `k_j ≥ 2^12 𝗀^j`. -/
theorem two_pow_twelve_mul_growthRatio_pow_le_level (j : ℕ) :
    2 ^ 12 * (growthRatio : ℝ) ^ j ≤ level j := by
  have hs := scale_late_lower j
  have hl : (scale j : ℝ) < 4 * level j + 4 := by
    exact_mod_cast scale_lt_four_mul_level_add_four j
  have hg : (1 : ℝ) ≤ (growthRatio : ℝ) ^ j := one_le_pow₀ one_lt_growthRatio_cast.le
  linarith

/-- For every `j ≥ N_*`, `k_j ≥ max n_0 (2^12 𝗀^j)`. -/
@[collatz_pos_dens "lem_level_late_lower"]
theorem level_late_lower {j : ℕ} (hj : generationThreshold ≤ j) :
    max (mxGateLevel : ℝ) (2 ^ 12 * (growthRatio : ℝ) ^ j) ≤ level j := by
  have hk := two_pow_twelve_mul_growthRatio_pow_le_level j
  refine max_le ?_ hk
  have hmono : (growthRatio : ℝ) ^ generationThreshold ≤ (growthRatio : ℝ) ^ j :=
    pow_le_pow_right₀ one_lt_growthRatio_cast.le hj
  exact (mxGateLevel_lt_two_pow_twelve_mul_growthRatio_pow.trans_le
    (mul_le_mul_of_nonneg_left hmono (by norm_num))).le.trans hk

end CollatzPosDens
