/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The packing mass `Q_pack`

The packing mass is the positive rational constant `Q_pack = 34267893/4480000`, the sum
`69003/17500 + 3795/1024` of two rational packing contributions.

## Main definitions

* `CollatzPosDens.Qpack`: the packing mass `Q_pack = 34267893/4480000 : ℚ`.

## Main results

* `CollatzPosDens.Qpack_eq`: the value `Q_pack = 34267893/4480000`.
* `CollatzPosDens.Qpack_cast`: the value of `(Q_pack : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Qpack_eq_add`: the decomposition `Q_pack = 69003/17500 + 3795/1024`.
* `CollatzPosDens.Qpack_pos`: `0 < Q_pack`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The packing mass `Q_pack := 34267893/4480000 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_Qpack"]
def Qpack : ℚ := 34267893 / 4480000

/-- The value of the packing mass. -/
@[simp]
theorem Qpack_eq : Qpack = 34267893 / 4480000 := rfl

/-- The value of the packing mass cast into a division ring of characteristic zero. -/
theorem Qpack_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (Qpack : K) = 34267893 / 4480000 := by
  simp [Qpack_eq]

/-- The packing mass is the sum `69003/17500 + 3795/1024` of the two packing contributions. -/
theorem Qpack_eq_add : Qpack = 69003 / 17500 + 3795 / 1024 := by norm_num

/-- The packing mass is positive. -/
theorem Qpack_pos : 0 < Qpack := by norm_num

end CollatzPosDens
