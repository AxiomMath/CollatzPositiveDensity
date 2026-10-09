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
# The colour scale `ε_*`

The colour scale is the positive rational constant `ε_* = 8/217`, used as the angle threshold
separating black from white points: a lattice point in the lower half is white when its angle
exceeds `ε_*` in absolute value, and black otherwise. It satisfies `0 < ε_* < 1/27`, since
`8 · 27 = 216 < 217`.

## Main definitions

* `CollatzPosDens.epsStar`: the colour scale `ε_* = 8/217 : ℚ`.

## Main results

* `CollatzPosDens.epsStar_eq`: the value `ε_* = 8/217`.
* `CollatzPosDens.epsStar_cast`: the value of `(ε_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.epsStar_pos`: `0 < ε_*`.
* `CollatzPosDens.epsStar_lt_one_div_27`: `ε_* < 1/27`.
* `CollatzPosDens.epsStar_lt_one_div_four`: `ε_* < 1/4`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The colour scale `ε_* := 8/217 ∈ ℚ_{>0}`, the angle threshold separating black from white
points. -/
@[collatz_pos_dens "def_eps_star"]
def epsStar : ℚ := 8 / 217

/-- The value of the colour scale. -/
@[simp]
theorem epsStar_eq : epsStar = 8 / 217 := rfl

/-- The value of the colour scale cast into a division ring of characteristic zero. -/
theorem epsStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (epsStar : K) = 8 / 217 := by
  simp [epsStar_eq]

/-- The colour scale is positive. -/
theorem epsStar_pos : 0 < epsStar := by norm_num

/-- The colour scale lies below `1/27`. -/
theorem epsStar_lt_one_div_27 : epsStar < 1 / 27 := by norm_num

/-- The colour scale lies below `1/4`. -/
theorem epsStar_lt_one_div_four : epsStar < 1 / 4 := by norm_num

end CollatzPosDens
