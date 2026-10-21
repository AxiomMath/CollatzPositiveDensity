/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.Recipe.S04Clog

/-!
# A lower bound for the scales

For every `j ∈ ℕ` the scale `b_j` satisfies
$$b_j \ge 16544\,\mathsf g^{\,j},$$
where `𝗀 = 101/100` is the physical growth ratio. Indeed geometric growth of the scales gives
`b_j = b_{0+j} ≥ 𝗀^j b_0`, and `b_0 = 16544`.

## Main results

* `CollatzPosDens.scale_late_lower`: `16544 𝗀^j ≤ b_j` for all `j`.
* `CollatzPosDens.fourteen_add_div_seventy_one_le_lg_scale`: `14 + ⌊t/71⌋ ≤ lg b_t`.

## Implementation notes

The inequality is stated in `ℝ`, with the rational ratio `𝗀` cast to `ℝ`, as in the
geometric growth bound it is derived from.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `j ∈ ℕ`, `b_j ≥ 16544 𝗀^j`. -/
@[collatz_pos_dens "lem_scales_late_lower"]
theorem scale_late_lower (j : ℕ) :
    16544 * (growthRatio : ℝ) ^ j ≤ scale j := by
  have h := scale_add_ge_growthRatio_pow_mul 0 j
  rw [zero_add, scale_zero, Nat.cast_ofNat] at h
  linarith

/-- For every `t ∈ ℕ`, `14 + ⌊t/71⌋ ≤ lg b_t`. -/
theorem fourteen_add_div_seventy_one_le_lg_scale (t : ℕ) :
    14 + t / 71 ≤ lg (scale t) := by
  have hg : (growthRatio : ℝ) ^ t * 16544 ≤ scale t := by
    linarith [scale_late_lower t]
  have h2 : (2 : ℝ) ^ (t / 71) ≤ (growthRatio : ℝ) ^ t := by
    calc (2 : ℝ) ^ (t / 71) ≤ ((growthRatio : ℝ) ^ 71) ^ (t / 71) := by
          gcongr; rw [growthRatio_cast]; norm_num
      _ = (growthRatio : ℝ) ^ (71 * (t / 71)) := by rw [pow_mul]
      _ ≤ (growthRatio : ℝ) ^ t :=
          pow_le_pow_right₀ one_lt_growthRatio_cast.le (Nat.mul_div_le t 71)
  have hlt : ((2 ^ (13 + t / 71) : ℕ) : ℝ) < scale t := by
    push_cast
    rw [pow_add]
    have : (0 : ℝ) < 2 ^ (t / 71) := by positivity
    nlinarith
  have hlt' : 2 ^ (13 + t / 71) < scale t := by exact_mod_cast hlt
  by_contra h
  have := lg_le_iff_le_two_pow.1 (show lg (scale t) ≤ 13 + t / 71 by omega)
  omega

end CollatzPosDens
