/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import CollatzPosDens.Attr

/-!
# The scale parameter `w_b`

For a natural number `b` this file defines the scale parameter
$$w_b = \lfloor 3b/5 \rfloor,$$
one of the rounded logarithmic scale parameters of the first-crossing argument [Mazur, §15.1].

## Main definitions

* `CollatzPosDens.wb`: the parameter `w_b = ⌊3b/5⌋`, computed as natural-number division.

## Main results

* `CollatzPosDens.wb_def`: the unfolding `w_b = 3 * b / 5`.
* `CollatzPosDens.wb_eq_floor`: `w_b` is the floor of `3b/5` in any linearly ordered semifield
  with a floor.
* `CollatzPosDens.five_mul_wb_le` and `CollatzPosDens.lt_five_mul_wb_add_one`: the defining
  inequalities `5 w_b ≤ 3b < 5 (w_b + 1)`.
* `CollatzPosDens.wb_le_self` and `CollatzPosDens.wb_mono`: `w_b ≤ b`, and `w_b` is monotone.

## Implementation notes

Natural-number division rounds down, so `3 * b / 5` is exactly `⌊3b/5⌋`; the agreement with the
floor of the quotient in any linearly ordered semifield is `wb_eq_floor`.

## References

* [Mazur, *Collatz positive density*], §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale parameter `w_b = ⌊3b/5⌋`, for `b : ℕ`. -/
@[collatz_pos_dens "def_wb"]
def wb (b : ℕ) : ℕ := 3 * b / 5

/-- Unfolding lemma for `wb`. -/
@[simp]
theorem wb_def (b : ℕ) : wb b = 3 * b / 5 := rfl

/-- `w_b` is the floor of `3b/5` computed in any linearly ordered semifield. -/
theorem wb_eq_floor {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorSemiring K] (b : ℕ) : wb b = ⌊(3 * b : K) / 5⌋₊ := by
  rw [wb_def, ← Nat.floor_div_eq_div (K := K)]
  push_cast
  rfl

/-- The lower defining inequality `5 w_b ≤ 3b`. -/
theorem five_mul_wb_le (b : ℕ) : 5 * wb b ≤ 3 * b := by
  rw [wb_def]; omega

/-- The upper defining inequality `3b < 5 (w_b + 1)`. -/
theorem lt_five_mul_wb_add_one (b : ℕ) : 3 * b < 5 * (wb b + 1) := by
  rw [wb_def]; omega

/-- `w_b ≤ b`. -/
theorem wb_le_self (b : ℕ) : wb b ≤ b := by
  rw [wb_def]; omega

/-- `w_b` is monotone in `b`. -/
theorem wb_mono : Monotone wb := fun _ _ h => Nat.div_le_div_right (by omega)

end CollatzPosDens
