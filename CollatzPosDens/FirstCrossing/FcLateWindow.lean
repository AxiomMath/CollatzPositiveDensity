/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.Width

/-!
# The central window `y^w_j`

For a scale index `j`, the central window is the integer
$$y^{\mathrm w}_j = \min\bigl(\mathrm{wd}(b_j), \lfloor b_j/8\rfloor\bigr),$$
where `b_j = CollatzPosDens.scale j` is the `j`-th scale and `wd` is the width.

## Main definitions

* `CollatzPosDens.yW`: the central window `min (wd b_j) ⌊b_j/8⌋ : ℤ`.

## Main results

* `CollatzPosDens.yW_le_wd`, `CollatzPosDens.yW_le_div_eight`: the two upper bounds.
* `CollatzPosDens.le_yW_iff`: `k ≤ y^w_j` exactly when `k` is below both bounds.
* `CollatzPosDens.yW_nonneg`, `CollatzPosDens.eight_mul_yW_le`: `0 ≤ y^w_j` and `8 y^w_j ≤ b_j`.
* `CollatzPosDens.yW_eq_natCast`: the window is the cast of the natural number
  `min (wd b_j) (b_j / 8)`.

## Implementation notes

The window is integer-valued; since both arguments of the minimum are natural numbers, it is
the cast of the corresponding natural-number minimum, and floor division by `8` is integer
division.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The **central window** `y^w_j = min(wd(b_j), ⌊b_j/8⌋) ∈ ℤ`. -/
@[collatz_pos_dens "def_fc_late_window"]
noncomputable def yW (j : ℕ) : ℤ :=
  min (wd (scale j) : ℤ) ((scale j : ℤ) / 8)

/-- The defining formula of `yW`. -/
theorem yW_def (j : ℕ) : yW j = min (wd (scale j) : ℤ) ((scale j : ℤ) / 8) := rfl

/-- The central window is the cast of `min (wd b_j) (b_j / 8)`. -/
theorem yW_eq_natCast (j : ℕ) : yW j = ((min (wd (scale j)) (scale j / 8) : ℕ) : ℤ) := by
  rw [yW_def, Nat.cast_min]
  norm_cast

/-- The central window is at most the width `wd(b_j)`. -/
theorem yW_le_wd (j : ℕ) : yW j ≤ wd (scale j) := min_le_left _ _

/-- The central window is at most `⌊b_j/8⌋`. -/
theorem yW_le_div_eight (j : ℕ) : yW j ≤ (scale j : ℤ) / 8 := min_le_right _ _

/-- `k ≤ y^w_j` exactly when `k ≤ wd(b_j)` and `k ≤ ⌊b_j/8⌋`. -/
theorem le_yW_iff {j : ℕ} {k : ℤ} :
    k ≤ yW j ↔ k ≤ wd (scale j) ∧ k ≤ (scale j : ℤ) / 8 :=
  le_min_iff

/-- The central window is nonnegative. -/
theorem yW_nonneg (j : ℕ) : 0 ≤ yW j := by
  rw [yW_eq_natCast]
  exact Int.natCast_nonneg _

/-- The central window satisfies `8 y^w_j ≤ b_j`. -/
theorem eight_mul_yW_le (j : ℕ) : 8 * yW j ≤ scale j := by
  have := yW_le_div_eight j
  omega

end CollatzPosDens
