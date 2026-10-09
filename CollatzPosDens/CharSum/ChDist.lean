/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Data.Int.Order.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints

/-!
# Distance to the cut-off

For a point `p : ℤ × ℤ` with coordinate `j(p) = CollatzPosDens.bkJ p` and a cut-off parameter
`n : ℕ`, the distance of `p` to the cut-off `⌊n/2⌋` is `d_J(p) = max(⌊n/2⌋ ∸ j(p), 1) ≥ 1`, where
`a ∸ b = max(a - b, 0)` is truncated subtraction.

## Main definitions

* `CollatzPosDens.chDist`: the distance `d_J(p)`, a natural number.

## Main results

* `CollatzPosDens.one_le_chDist`: `1 ≤ d_J(p)`.
* `CollatzPosDens.chDist_le`: if `⌊n/2⌋ ∸ j(p) ≤ m` then `d_J(p) ≤ max(m, 1)`.
* `CollatzPosDens.chDist_eq_of_lt`: if `j(p) < ⌊n/2⌋` then `d_J(p) = ⌊n/2⌋ - j(p)`.
* `CollatzPosDens.chDist_eq_one_of_le`: if `⌊n/2⌋ - 1 ≤ j(p)` then `d_J(p) = 1`.

## Implementation notes

Since `j(p)` is an integer, the truncated difference `⌊n/2⌋ ∸ j(p)` is `Int.toNat` of the
integer difference, which is `max(⌊n/2⌋ - j(p), 0)`. The value is a natural number, with lower
bound `one_le_chDist`, and the definition is stated for all `p : ℤ × ℤ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The distance to the cut-off `d_J(p) = max(⌊n/2⌋ ∸ j(p), 1)`,
where `a ∸ b = max(a - b, 0)`. -/
@[collatz_pos_dens "def_ch_dist"]
def chDist (n : ℕ) (p : ℤ × ℤ) : ℕ := max ((n / 2 : ℕ) - bkJ p).toNat 1

/-- Unfolding `d_J(p)` with the truncated subtraction written as `max (· - ·) 0`. -/
theorem chDist_eq (n : ℕ) (p : ℤ × ℤ) :
    (chDist n p : ℤ) = max (max ((n / 2 : ℕ) - bkJ p) 0) 1 := by
  simp [chDist]

/-- The distance `d_J(p)` is at least `1`. -/
@[simp]
theorem one_le_chDist (n : ℕ) (p : ℤ × ℤ) : 1 ≤ chDist n p := le_max_right _ _

/-- The distance `d_J(p)` is positive. -/
theorem chDist_pos (n : ℕ) (p : ℤ × ℤ) : 0 < chDist n p := one_le_chDist n p

/-- The distance `d_J(p)` is nonzero. -/
@[simp]
theorem chDist_ne_zero (n : ℕ) (p : ℤ × ℤ) : chDist n p ≠ 0 := (chDist_pos n p).ne'

/-- If `⌊n/2⌋ ∸ j(p) ≤ m`, then `d_J(p) ≤ max(m, 1)`. -/
theorem chDist_le {n m : ℕ} {p : ℤ × ℤ} (h : ((n / 2 : ℕ) : ℤ) - bkJ p ≤ m) :
    chDist n p ≤ max m 1 := by
  unfold chDist
  exact max_le_max (by omega) le_rfl

/-- Away from the cut-off, `d_J(p) = ⌊n/2⌋ - j(p)`. -/
theorem chDist_eq_of_lt {n : ℕ} {p : ℤ × ℤ} (h : bkJ p < ((n / 2 : ℕ) : ℤ)) :
    (chDist n p : ℤ) = ((n / 2 : ℕ) : ℤ) - bkJ p := by
  rw [chDist_eq]
  omega

/-- If `⌊n/2⌋ - 1 ≤ j(p)`, then `d_J(p) = 1`. -/
theorem chDist_eq_one_of_le {n : ℕ} {p : ℤ × ℤ} (h : ((n / 2 : ℕ) : ℤ) - 1 ≤ bkJ p) :
    chDist n p = 1 := by
  have := chDist_eq n p
  omega

end CollatzPosDens
