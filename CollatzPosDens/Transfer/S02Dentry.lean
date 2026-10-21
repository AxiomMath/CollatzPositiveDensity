/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The entry decrement `dEntry`

The entry decrement is the rational constant `dEntry = 23/100`, with contraction factor
`1 - dEntry = 77/100`.

## Main definitions

* `CollatzPosDens.dEntry`: the entry decrement `23/100 : ℚ`.

## Main results

* `CollatzPosDens.dEntry_eq`: the value `dEntry = 23/100`.
* `CollatzPosDens.dEntry_cast`: the value `(dEntry : K) = 23/100` in any division ring `K` of
  characteristic zero.
* `CollatzPosDens.one_sub_dEntry`: `1 - dEntry = 77/100`.
* `CollatzPosDens.dEntry_pos`, `CollatzPosDens.dEntry_lt_one`: `0 < dEntry < 1`.
-/
@[expose] public section

namespace CollatzPosDens

/-- The entry decrement `dEntry = 23/100 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_dentry"]
def dEntry : ℚ := 23 / 100

/-- The value of the entry decrement. -/
@[simp]
theorem dEntry_eq : dEntry = 23 / 100 := rfl

/-- The value of the entry decrement cast into a division ring of characteristic zero. -/
theorem dEntry_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (dEntry : K) = 23 / 100 := by
  simp [dEntry_eq]

/-- The contraction factor `1 - dEntry = 77/100`. -/
theorem one_sub_dEntry : 1 - dEntry = 77 / 100 := by norm_num

/-- The entry decrement is positive. -/
theorem dEntry_pos : 0 < dEntry := by norm_num

/-- The entry decrement is less than one. -/
theorem dEntry_lt_one : dEntry < 1 := by norm_num

end CollatzPosDens
