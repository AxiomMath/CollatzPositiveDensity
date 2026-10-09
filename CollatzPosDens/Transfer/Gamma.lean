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

The trace tilt is the positive rational constant `γ_* = 87/200`, the exponent of the exponential
tilt applied to the weight of a trace.

## Main definitions

* `CollatzPosDens.gammaStar`: the trace tilt `γ_* = 87/200 : ℚ`.

## Main results

* `CollatzPosDens.gammaStar_eq`: the value `γ_* = 87/200`.
* `CollatzPosDens.gammaStar_cast`: the value of `(γ_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.gammaStar_pos`: `0 < γ_*`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The trace tilt `γ_* := 87/200 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_gamma"]
def gammaStar : ℚ := 87 / 200

/-- The value of the trace tilt. -/
@[simp]
theorem gammaStar_eq : gammaStar = 87 / 200 := rfl

/-- The value of the trace tilt cast into a division ring of characteristic zero. -/
theorem gammaStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (gammaStar : K) = 87 / 200 := by
  simp [gammaStar_eq]

/-- The trace tilt is positive. -/
theorem gammaStar_pos : 0 < gammaStar := by norm_num

end CollatzPosDens
