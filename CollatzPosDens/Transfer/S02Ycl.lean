/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The clearing point

For each Fourier parameter index `ι : FIndex`, the clearing point `clearingPoint ι` is a rational
constant in the open unit interval: `clearingPoint .o = 8191/8192 = 1 - 2⁻¹³` and
`clearingPoint .b = 255/256 = 1 - 2⁻⁸`. Since it is less than one, the power
`clearingPoint ι ^ n` is decreasing in `n`.

## Main definitions

* `CollatzPosDens.clearingPoint`: the clearing point of an index, a rational number.

## Main results

* `CollatzPosDens.clearingPoint_o`, `CollatzPosDens.clearingPoint_b`: the values
  `8191/8192` and `255/256`.
* `CollatzPosDens.one_sub_clearingPoint_o`, `CollatzPosDens.one_sub_clearingPoint_b`:
  the complements `1/8192` and `1/256`.
* `CollatzPosDens.clearingPoint_cast_o`, `CollatzPosDens.clearingPoint_cast_b`: the values cast
  into any division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.clearingPoint_pos`, `CollatzPosDens.clearingPoint_lt_one`:
  `0 < clearingPoint ι < 1`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clearing point of the Fourier parameter index `ι`, a rational number: `8191/8192` at `.o`
and `255/256` at `.b`. -/
@[collatz_pos_dens "def_s02_ycl"]
def clearingPoint : FIndex → ℚ
  | .o => 8191 / 8192
  | .b => 255 / 256

/-- The clearing point at the original index. -/
@[simp]
theorem clearingPoint_o : clearingPoint .o = 8191 / 8192 := rfl

/-- The clearing point at the bootstrap index. -/
@[simp]
theorem clearingPoint_b : clearingPoint .b = 255 / 256 := rfl

/-- At the original index, `1 - clearingPoint .o = 1/8192`. -/
theorem one_sub_clearingPoint_o : 1 - clearingPoint .o = 1 / 8192 := by norm_num

/-- At the bootstrap index, `1 - clearingPoint .b = 1/256`. -/
theorem one_sub_clearingPoint_b : 1 - clearingPoint .b = 1 / 256 := by norm_num

/-- The clearing point at the original index, cast into a division ring of characteristic
zero. -/
theorem clearingPoint_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (clearingPoint .o : K) = 8191 / 8192 := by
  simp [clearingPoint_o]

/-- The clearing point at the bootstrap index, cast into a division ring of characteristic
zero. -/
theorem clearingPoint_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (clearingPoint .b : K) = 255 / 256 := by
  simp [clearingPoint_b]

/-- The clearing point is positive. -/
theorem clearingPoint_pos (ι : FIndex) : 0 < clearingPoint ι := by
  cases ι <;> norm_num

/-- The clearing point is nonnegative. -/
theorem clearingPoint_nonneg (ι : FIndex) : 0 ≤ clearingPoint ι := (clearingPoint_pos ι).le

/-- The clearing point is less than one. -/
theorem clearingPoint_lt_one (ι : FIndex) : clearingPoint ι < 1 := by
  cases ι <;> norm_num

/-- The clearing point is at most one. -/
theorem clearingPoint_le_one (ι : FIndex) : clearingPoint ι ≤ 1 := (clearingPoint_lt_one ι).le

/-- The clearing point is less than two. -/
theorem clearingPoint_lt_two (ι : FIndex) : clearingPoint ι < 2 := by
  cases ι <;> norm_num

end CollatzPosDens
