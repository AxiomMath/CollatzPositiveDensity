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
# The decay exponent `A_*`

The decay exponent is the positive rational constant `A_* = 10241/4096`, lying strictly between
`2` and `3`.

## Main definitions

* `CollatzPosDens.Aexp`: the decay exponent `A_* = 10241/4096 : ℚ`.

## Main results

* `CollatzPosDens.Aexp_eq`: the value `A_* = 10241/4096`.
* `CollatzPosDens.Aexp_cast`: the value of `(A_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Aexp_pos`, `CollatzPosDens.two_lt_Aexp`,
  `CollatzPosDens.Aexp_lt_three`: the bounds `0 < 2 < A_* < 3`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The decay exponent `A_* := 10241/4096 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_Aexp"]
def Aexp : ℚ := 10241 / 4096

/-- The value of the decay exponent. -/
@[simp]
theorem Aexp_eq : Aexp = 10241 / 4096 := rfl

/-- The value of the decay exponent cast into a division ring of characteristic zero. -/
theorem Aexp_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (Aexp : K) = 10241 / 4096 := by
  simp [Aexp_eq]

/-- The decay exponent is positive. -/
theorem Aexp_pos : 0 < Aexp := by norm_num

/-- The decay exponent exceeds `2`. -/
theorem two_lt_Aexp : 2 < Aexp := by norm_num

/-- The decay exponent is below `3`. -/
theorem Aexp_lt_three : Aexp < 3 := by norm_num

end CollatzPosDens
