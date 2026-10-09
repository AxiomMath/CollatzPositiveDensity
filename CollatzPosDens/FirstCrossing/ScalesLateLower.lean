/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesB444
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.Recipe.Clog

/-!
# A lower bound for the late scales

For every `j ≥ 444` the scale `b_j` satisfies
$$b_j > 190\,\mathsf g^{\,j},$$
where `𝗀 = 101/100` is the physical growth ratio. Indeed, geometric growth of the scales gives
`b_j ≥ 𝗀^{j-444} b_{444}`, and `b_{444} = 16544 > 190 𝗀^{444}`, the last comparison being the
exact inequality `16544 · 100^{444} > 190 · 101^{444}`.

## Main results

* `CollatzPosDens.scale_late_lower`: `190 𝗀^j < b_j` for all `j ≥ 444`.
* `CollatzPosDens.fourteen_add_div_seventy_one_le_lg_scale`: `14 + ⌊t/71⌋ ≤ lg b_{444+t}`.

## Implementation notes

The inequality is stated in `ℝ`, with the rational ratio `𝗀` cast to `ℝ`, as in the
geometric growth bound it is derived from.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `j ≥ 444`, the scale `b_j` exceeds `190 𝗀^j`. -/
@[collatz_pos_dens "lem_scales_late_lower"]
theorem scale_late_lower {j : ℕ} (hj : 444 ≤ j) :
    190 * (growthRatio : ℝ) ^ j < scale j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hgrow := scale_add_ge_growthRatio_pow_mul 444 k
  rw [scale_444] at hgrow
  have hnum : 190 * (growthRatio : ℝ) ^ 444 < 16544 := by
    have h : (190 * 101 ^ 444 : ℕ) < 16544 * 100 ^ 444 := by decide +kernel
    rw [growthRatio_cast, div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
    exact_mod_cast h
  have hk : 0 < (growthRatio : ℝ) ^ k := pow_pos growthRatio_cast_pos k
  calc 190 * (growthRatio : ℝ) ^ (444 + k)
      = (growthRatio : ℝ) ^ k * (190 * (growthRatio : ℝ) ^ 444) := by ring
    _ < (growthRatio : ℝ) ^ k * 16544 := by gcongr
    _ ≤ scale (444 + k) := by exact_mod_cast hgrow

/-- For `j = 444 + t`, `14 + ⌊t/71⌋ ≤ lg b_j`. -/
theorem fourteen_add_div_seventy_one_le_lg_scale (t : ℕ) :
    14 + t / 71 ≤ lg (scale (444 + t)) := by
  have hg : (growthRatio : ℝ) ^ t * 16544 ≤ scale (444 + t) := by
    have := scale_add_ge_growthRatio_pow_mul 444 t
    rwa [scale_444, Nat.cast_ofNat] at this
  have h2 : (2 : ℝ) ^ (t / 71) ≤ (growthRatio : ℝ) ^ t := by
    calc (2 : ℝ) ^ (t / 71) ≤ ((growthRatio : ℝ) ^ 71) ^ (t / 71) := by
          gcongr; rw [growthRatio_cast]; norm_num
      _ = (growthRatio : ℝ) ^ (71 * (t / 71)) := by rw [pow_mul]
      _ ≤ (growthRatio : ℝ) ^ t :=
          pow_le_pow_right₀ one_lt_growthRatio_cast.le (Nat.mul_div_le t 71)
  have hlt : ((2 ^ (13 + t / 71) : ℕ) : ℝ) < scale (444 + t) := by
    push_cast
    rw [pow_add]
    have : (0 : ℝ) < 2 ^ (t / 71) := by positivity
    nlinarith
  have hlt' : 2 ^ (13 + t / 71) < scale (444 + t) := by exact_mod_cast hlt
  by_contra h
  have := lg_le_iff_le_two_pow.1 (show lg (scale (444 + t)) ≤ 13 + t / 71 by omega)
  omega

end CollatzPosDens
