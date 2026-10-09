/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import Mathlib.Tactic.IntervalCases

/-!
# Lattice points at distance at most one are cardinal neighbours

Two distinct lattice points `p ≠ q` with `|p - q| ≤ 1` differ by a unit step in exactly one
coordinate: `|j(p) - j(q)| + |l(p) - l(q)| = 1`. Indeed the coordinate differences `x, y` are
integers with `0 < x² + y² ≤ 1`, and a nonzero integer has square at least `1`.

## Main results

* `CollatzPosDens.abs_bkJ_sub_add_abs_bkL_sub_eq_one`: if `p ≠ q` and `|p - q| ≤ 1`, then
  `|j(p) - j(q)| + |l(p) - l(q)| = 1`.
* `CollatzPosDens.abs_bkJ_sub_add_abs_bkL_sub_eq_one_of_bkDistSq_le`: the same conclusion
  from the integer hypothesis `bkDistSq p q ≤ 1`.

## Implementation notes

Membership of `p` and `q` in `𝒫` plays no role, so the statements are for arbitrary points of
`ℤ × ℤ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `p ≠ q` and `|p - q|² ≤ 1`, then `|j(p) - j(q)| + |l(p) - l(q)| = 1`. -/
theorem abs_bkJ_sub_add_abs_bkL_sub_eq_one_of_bkDistSq_le {p q : ℤ × ℤ} (hpq : p ≠ q)
    (h : bkDistSq p q ≤ 1) : |bkJ p - bkJ q| + |bkL p - bkL q| = 1 := by
  have hne : bkDistSq p q ≠ 0 := fun h0 => hpq (bkDistSq_eq_zero_iff.1 h0)
  unfold bkDistSq at h hne
  generalize bkJ p - bkJ q = x at *
  generalize bkL p - bkL q = y at *
  have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  have hx2 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hy1 : -1 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg (y + 1)]
  have hy2 : y ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  interval_cases x <;> interval_cases y <;> simp_all

/-- **Cardinal neighbours.** If `p ≠ q` and `|p - q| ≤ 1`, then
`|j(p) - j(q)| + |l(p) - l(q)| = 1`. -/
@[collatz_pos_dens "lem_bk_cardinal"]
theorem abs_bkJ_sub_add_abs_bkL_sub_eq_one {p q : ℤ × ℤ} (hpq : p ≠ q) (h : bkDist p q ≤ 1) :
    |bkJ p - bkJ q| + |bkL p - bkL q| = 1 := by
  refine abs_bkJ_sub_add_abs_bkL_sub_eq_one_of_bkDistSq_le hpq ?_
  have hsq : (bkDistSq p q : ℝ) ≤ 1 := by
    rw [← bkDist_sq]
    nlinarith [bkDist_nonneg p q]
  exact_mod_cast hsq

end CollatzPosDens
