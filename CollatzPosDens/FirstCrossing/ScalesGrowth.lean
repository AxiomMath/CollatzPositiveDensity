/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.EbLower
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Geometric growth of the scales

The scales `b_j` grow at least geometrically with ratio `𝗀 = 101/100`: for all `i, j ∈ ℕ`,
$$b_{i+j} \ge \mathsf g^{\,j} \, b_i.$$
Every scale is at least `b_0 = 16544 ≥ 1`, and `e_b ≥ b/100` for every `b ≥ 1`, so one step
of the recursion `b_{t+1} = b_t + e_{b_t}` gives `b_{t+1} ≥ b_t + b_t/100 = 𝗀 b_t`; the general
bound follows by induction on `j`.

## Main results

* `CollatzPosDens.scale_succ_ge_growthRatio_mul`: `𝗀 b_t ≤ b_{t+1}`.
* `CollatzPosDens.scale_add_ge_growthRatio_pow_mul`: `𝗀^j b_i ≤ b_{i+j}`.

## Implementation notes

The inequality is stated in `ℝ`, with the rational ratio `𝗀` cast to `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- One step of the scales multiplies by at least `𝗀`: `𝗀 b_t ≤ b_{t+1}`. -/
theorem scale_succ_ge_growthRatio_mul (t : ℕ) :
    (growthRatio : ℝ) * scale t ≤ scale (t + 1) := by
  have h := (le_max_right _ _).trans (eb_lower (scale_pos t))
  rw [growthRatio_cast, scale_succ]
  push_cast
  linarith

/-- The scales grow geometrically: for all `i, j ∈ ℕ`, `𝗀^j b_i ≤ b_{i+j}`. -/
@[collatz_pos_dens "lem_scales_growth"]
theorem scale_add_ge_growthRatio_pow_mul (i j : ℕ) :
    (growthRatio : ℝ) ^ j * scale i ≤ scale (i + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc (growthRatio : ℝ) ^ (j + 1) * scale i
        = (growthRatio : ℝ) * ((growthRatio : ℝ) ^ j * scale i) := by ring
      _ ≤ (growthRatio : ℝ) * scale (i + j) :=
          mul_le_mul_of_nonneg_left ih growthRatio_cast_pos.le
      _ ≤ scale (i + j + 1) := scale_succ_ge_growthRatio_mul (i + j)

end CollatzPosDens
