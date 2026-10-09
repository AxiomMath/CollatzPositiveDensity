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
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# A lower bound for the late levels

For every `j ≥ 444` the residue level `k_j = ⌊b_j / 4⌋` satisfies
$$k_j \ge 47\,\mathsf g^{\,j},$$
where `𝗀 = 101/100` is the physical growth ratio. Indeed `k_j ≥ b_j/4 - 1 > 47.5 𝗀^j - 1` by
the late lower bound `b_j > 190 𝗀^j` on the scales, and `47.5 𝗀^j - 1 ≥ 47 𝗀^j` because
`𝗀^j ≥ 𝗀^{444} ≥ 2`.

## Main results

* `CollatzPosDens.level_late_lower`: `47 𝗀^j ≤ k_j` for all `j ≥ 444`.

## Implementation notes

The inequality is stated in `ℝ`, with the rational ratio `𝗀` and the natural-number level cast
to `ℝ`. The bound `𝗀^j ≥ 2` is obtained from Bernoulli's inequality `𝗀^j ≥ 1 + j/100`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `j ≥ 444`, the level satisfies `47 𝗀^j ≤ level j`. -/
@[collatz_pos_dens "lem_level_late_lower"]
theorem level_late_lower {j : ℕ} (hj : 444 ≤ j) :
    47 * (growthRatio : ℝ) ^ j ≤ level j := by
  have hs := scale_late_lower hj
  have hl : (scale j : ℝ) < 4 * level j + 4 := by
    exact_mod_cast scale_lt_four_mul_level_add_four j
  have hbern : 1 + (j : ℝ) * (1 / 100) ≤ (growthRatio : ℝ) ^ j := by
    have := one_add_mul_le_pow (a := (1 / 100 : ℝ)) (by norm_num) j
    rw [growthRatio_cast]
    convert this using 2; norm_num [add_comm]
  have hj' : (444 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

end CollatzPosDens
