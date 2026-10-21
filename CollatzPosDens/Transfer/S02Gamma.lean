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
# The trace tilt `γ_*`

The trace tilt, the rate of the reward discount of the trace, is the rational constant
`γ_* = 133/3125`. It is the exponent of the tilted weight `exp (-γ_* N*)` attached to a trace.

## Main definitions

* `CollatzPosDens.gammaStar`: the trace tilt `γ_* = 133/3125 : ℚ`.

## Main results

* `CollatzPosDens.gammaStar_eq`: the value `γ_* = 133/3125`.
* `CollatzPosDens.gammaStar_cast`: the value of `(γ_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.gammaStar_pos`: `0 < γ_*`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The trace tilt `γ_* := 133/3125 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_gamma"]
def gammaStar : ℚ := 133 / 3125

/-- The value of the trace tilt. -/
@[simp]
theorem gammaStar_eq : gammaStar = 133 / 3125 := rfl

/-- The value of the trace tilt cast into a division ring of characteristic zero. -/
theorem gammaStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (gammaStar : K) = 133 / 3125 := by
  simp

/-- The trace tilt is positive. -/
theorem gammaStar_pos : 0 < gammaStar := by norm_num

end CollatzPosDens
