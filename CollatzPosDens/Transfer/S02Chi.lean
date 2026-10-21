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
# The envelope allowance `χ_*`

The envelope allowance is the positive rational constant `χ_* = 63/2500`, the allowance for
the envelope factors of the white and near-top cases.

## Main definitions

* `CollatzPosDens.chiStar`: the envelope allowance `χ_* = 63/2500 : ℚ`.

## Main results

* `CollatzPosDens.chiStar_eq`: the value `χ_* = 63/2500`.
* `CollatzPosDens.chiStar_cast`: the value of `(χ_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.chiStar_pos`, `CollatzPosDens.chiStar_lt_one`: the bounds `0 < χ_* < 1`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The envelope allowance `χ_* := 63/2500 ∈ ℚ`, the allowance for the envelope factors of the
white and near-top cases. -/
@[collatz_pos_dens "def_s02_chi"]
def chiStar : ℚ := 63 / 2500

/-- The value of the envelope allowance. -/
@[simp]
theorem chiStar_eq : chiStar = 63 / 2500 := rfl

/-- The value of the envelope allowance cast into a division ring of characteristic zero. -/
theorem chiStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (chiStar : K) = 63 / 2500 := by
  simp [chiStar_eq]

/-- The envelope allowance is positive. -/
theorem chiStar_pos : 0 < chiStar := by norm_num

/-- The envelope allowance is below `1`. -/
theorem chiStar_lt_one : chiStar < 1 := by norm_num

end CollatzPosDens
