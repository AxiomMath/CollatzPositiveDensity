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
# The vertical deviation slope `η_dv`

For each Fourier index `ι : FIndex`, the vertical deviation slope `devEta ι` is a positive
rational constant: `devEta .o = 6579 / 500` and `devEta .b = 1653 / 125`.

## Main definitions

* `CollatzPosDens.devEta`: the vertical deviation slope `η_dv(ι) : ℚ`, with
  `η_dv(o) = 6579 / 500` and `η_dv(b) = 1653 / 125`.

## Main results

* `CollatzPosDens.devEta_o`, `CollatzPosDens.devEta_b`: the two values.
* `CollatzPosDens.devEta_cast_o`, `CollatzPosDens.devEta_cast_b`: the two values cast into a
  division ring of characteristic zero.
* `CollatzPosDens.devEta_pos`, `CollatzPosDens.devEta_nonneg`: `η_dv(ι)` is positive.
-/

@[expose] public section

namespace CollatzPosDens

/-- The vertical deviation slope `η_dv(ι) ∈ ℚ`: `η_dv(o) := 6579/500` and
`η_dv(b) := 1653/125`. -/
@[collatz_pos_dens "def_s02_dev_eta"]
def devEta : FIndex → ℚ
  | .o => 6579 / 500
  | .b => 1653 / 125

/-- The value of `η_dv` at the original index `o`. -/
@[simp]
theorem devEta_o : devEta .o = 6579 / 500 := rfl

/-- The value of `η_dv` at the bootstrap index `b`. -/
@[simp]
theorem devEta_b : devEta .b = 1653 / 125 := rfl

/-- The value of `η_dv(o)` cast into a division ring of characteristic zero. -/
theorem devEta_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (devEta .o : K) = 6579 / 500 := by
  simp [devEta_o]

/-- The value of `η_dv(b)` cast into a division ring of characteristic zero. -/
theorem devEta_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (devEta .b : K) = 1653 / 125 := by
  simp [devEta_b]

/-- `η_dv(ι)` is positive. -/
theorem devEta_pos (ι : FIndex) : 0 < devEta ι := by
  cases ι <;> norm_num

/-- `η_dv(ι)` is nonnegative. -/
theorem devEta_nonneg (ι : FIndex) : 0 ≤ devEta ι := (devEta_pos ι).le

end CollatzPosDens
