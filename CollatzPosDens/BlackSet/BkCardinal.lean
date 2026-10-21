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
# Cardinal neighbours

Two points `p, v` of the lattice are *cardinal neighbours* if they differ by a unit step in
exactly one coordinate, that is `|j(p) - j(v)| + |l(p) - l(v)| = 1`. Distinct lattice points at
Euclidean distance at most `1` are cardinal neighbours: the coordinate differences `x, y` are
integers with `0 < x² + y² ≤ 1`, and a nonzero integer has square at least `1`.

## Main definitions

* `CollatzPosDens.BkCardinalNeighbour`: `p` and `v` are cardinal neighbours,
  `|j(p) - j(v)| + |l(p) - l(v)| = 1`.

## Main results

* `CollatzPosDens.BkCardinalNeighbour.symm`, `CollatzPosDens.BkCardinalNeighbour.ne`: the
  relation is symmetric and irreflexive.
* `CollatzPosDens.bkCardinalNeighbour_iff_bkDistSq_eq_one`: cardinal neighbours are exactly the
  points at squared distance `1`.
* `CollatzPosDens.abs_bkJ_sub_add_abs_bkL_sub_eq_one`: if `p ≠ q` and `|p - q| ≤ 1`, then
  `|j(p) - j(q)| + |l(p) - l(q)| = 1`.
* `CollatzPosDens.abs_bkJ_sub_add_abs_bkL_sub_eq_one_of_bkDistSq_le`: the same conclusion
  from the integer hypothesis `bkDistSq p q ≤ 1`.

## Implementation notes

Cardinal neighbours are only used for points `p, v ∈ 𝒫`, but membership in `𝒫` plays no role,
so the relation is defined on all of `ℤ × ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/
@[expose] public section

namespace CollatzPosDens

/-- Two points `p, v` are *cardinal neighbours* if `|j(p) - j(v)| + |l(p) - l(v)| = 1`. -/
@[collatz_pos_dens "def_bk_cardinal"]
def BkCardinalNeighbour (p v : ℤ × ℤ) : Prop :=
  |bkJ p - bkJ v| + |bkL p - bkL v| = 1

/-- `p` and `v` are cardinal neighbours iff `|j(p) - j(v)| + |l(p) - l(v)| = 1`. -/
theorem bkCardinalNeighbour_iff {p v : ℤ × ℤ} :
    BkCardinalNeighbour p v ↔ |bkJ p - bkJ v| + |bkL p - bkL v| = 1 := Iff.rfl

/-- Being cardinal neighbours is decidable. -/
instance (p v : ℤ × ℤ) : Decidable (BkCardinalNeighbour p v) :=
  inferInstanceAs (Decidable (_ = _))

/-- Being cardinal neighbours is a symmetric relation. -/
theorem BkCardinalNeighbour.symm {p v : ℤ × ℤ} (h : BkCardinalNeighbour p v) :
    BkCardinalNeighbour v p := by
  rwa [BkCardinalNeighbour, abs_sub_comm (bkJ v), abs_sub_comm (bkL v)]

/-- `p` and `v` are cardinal neighbours iff `v` and `p` are. -/
theorem bkCardinalNeighbour_comm {p v : ℤ × ℤ} :
    BkCardinalNeighbour p v ↔ BkCardinalNeighbour v p :=
  ⟨.symm, .symm⟩

/-- A point is not its own cardinal neighbour. -/
theorem BkCardinalNeighbour.ne {p v : ℤ × ℤ} (h : BkCardinalNeighbour p v) : p ≠ v := by
  rintro rfl
  simp [BkCardinalNeighbour] at h

/-- Cardinal neighbours are exactly the points at squared distance `1`. -/
theorem bkCardinalNeighbour_iff_bkDistSq_eq_one {p v : ℤ × ℤ} :
    BkCardinalNeighbour p v ↔ bkDistSq p v = 1 := by
  unfold BkCardinalNeighbour bkDistSq
  generalize bkJ p - bkJ v = x
  generalize bkL p - bkL v = y
  constructor
  · intro h
    have hx : |x| ≤ 1 := by linarith [abs_nonneg y]
    have hy : |y| ≤ 1 := by linarith [abs_nonneg x]
    rw [abs_le] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    interval_cases x <;> interval_cases y <;> simp_all
  · intro h
    have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
    have hx2 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
    have hy1 : -1 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg (y + 1)]
    have hy2 : y ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
    interval_cases x <;> interval_cases y <;> simp_all

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

/-- If `p ≠ q` and `|p - q| ≤ 1`, then `|j(p) - j(q)| + |l(p) - l(q)| = 1`. -/
theorem abs_bkJ_sub_add_abs_bkL_sub_eq_one {p q : ℤ × ℤ} (hpq : p ≠ q) (h : bkDist p q ≤ 1) :
    |bkJ p - bkJ q| + |bkL p - bkL q| = 1 := by
  refine abs_bkJ_sub_add_abs_bkL_sub_eq_one_of_bkDistSq_le hpq ?_
  have hsq : (bkDistSq p q : ℝ) ≤ 1 := by
    rw [← bkDist_sq]
    nlinarith [bkDist_nonneg p q]
  exact_mod_cast hsq

/-- Distinct points at distance at most `1` are cardinal neighbours. -/
theorem bkCardinalNeighbour_of_bkDist_le {p q : ℤ × ℤ} (hpq : p ≠ q) (h : bkDist p q ≤ 1) :
    BkCardinalNeighbour p q :=
  abs_bkJ_sub_add_abs_bkL_sub_eq_one hpq h

end CollatzPosDens
