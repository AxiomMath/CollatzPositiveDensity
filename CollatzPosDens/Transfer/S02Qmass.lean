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
# The paid initial mass `q_mass`

The paid initial mass is the positive rational constant `q_mass = 38177/125000`, a bound on the
total mass of the paid initial-row profile of a black pair of large gap.

## Main definitions

* `CollatzPosDens.qMass`: the paid initial mass `q_mass = 38177/125000 : ℚ`.

## Main results

* `CollatzPosDens.qMass_eq`: the value `q_mass = 38177/125000`.
* `CollatzPosDens.qMass_cast`: the value of `(q_mass : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.qMass_pos`, `CollatzPosDens.qMass_lt_one`: the bounds `0 < q_mass < 1`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The paid initial mass `q_mass := 38177/125000 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_qmass"]
def qMass : ℚ := 38177 / 125000

/-- The value of the paid initial mass. -/
@[simp]
theorem qMass_eq : qMass = 38177 / 125000 := rfl

/-- The value of the paid initial mass cast into a division ring of characteristic zero. -/
theorem qMass_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (qMass : K) = 38177 / 125000 := by
  simp [qMass_eq]

/-- The paid initial mass is positive. -/
theorem qMass_pos : 0 < qMass := by norm_num

/-- The paid initial mass is below `1`. -/
theorem qMass_lt_one : qMass < 1 := by norm_num

end CollatzPosDens
