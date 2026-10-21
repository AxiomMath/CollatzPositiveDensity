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
# The packing discrepancy constant `Γ_pk`

The rational constant `Γ_pk = 2113/500` is the additive discrepancy of the packing bound: for
every packing state `s` and every `N ≥ 36` the stopping-time cost obeys
`(4 - S_s) N + D_s ≤ 4 q_pack N + Γ_pk`.

## Main definitions

* `CollatzPosDens.Gammapk`: the packing discrepancy constant `Γ_pk = 2113/500 : ℚ`.

## Main results

* `CollatzPosDens.Gammapk_eq`: the value `Γ_pk = 2113/500`.
* `CollatzPosDens.Gammapk_cast`: the value of `(Γ_pk : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Gammapk_pos`: `0 < Γ_pk`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The packing discrepancy constant `Γ_pk := 2113/500 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_Gamma"]
def Gammapk : ℚ := 2113 / 500

/-- The value of the packing discrepancy constant. -/
@[simp]
theorem Gammapk_eq : Gammapk = 2113 / 500 := rfl

/-- The value of the packing discrepancy constant cast into a division ring of characteristic
zero, e.g. `ℝ`. -/
theorem Gammapk_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (Gammapk : K) = 2113 / 500 := by
  simp

/-- The packing discrepancy constant is positive. -/
theorem Gammapk_pos : 0 < Gammapk := by norm_num

end CollatzPosDens
