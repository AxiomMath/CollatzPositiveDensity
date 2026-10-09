/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Tactic.NormNum

/-!
# The second-letter tilt ratio

This file defines the rational constant `κ_* = 4/25`, the ratio by which the exponential tilt
`γ_*` is scaled on the second letter of a passage, and records its value and elementary bounds.

## Main definitions

* `CollatzPosDens.kappaStar`: the rational number `κ_* = 4/25`.

## Main results

* `CollatzPosDens.kappaStar_cast`: the value of `(κ_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.kappaStar_pos`: `0 < κ_*`.
* `CollatzPosDens.kappaStar_nonneg`: `0 ≤ κ_*`.
* `CollatzPosDens.kappaStar_lt_one`: `κ_* < 1`.

## Implementation notes

The constant is defined in `ℚ`, so that rational expressions in it can be evaluated exactly;
`CollatzPosDens.kappaStar_cast` gives its value in `ℝ` or any other division ring of
characteristic zero.
-/

@[expose] public section

namespace CollatzPosDens

/-- The second-letter tilt ratio `κ_* = 4/25`. -/
@[collatz_pos_dens "def_s02_kappa"]
def kappaStar : ℚ := 4 / 25

/-- The tilt ratio `κ_*` equals `4/25`. -/
theorem kappaStar_def : kappaStar = 4 / 25 := rfl

/-- The value of the tilt ratio `κ_*` cast into a division ring of characteristic zero. -/
theorem kappaStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (kappaStar : K) = 4 / 25 := by
  simp [kappaStar_def]

/-- The tilt ratio `κ_*` is positive. -/
theorem kappaStar_pos : 0 < kappaStar := by
  rw [kappaStar_def]; norm_num

/-- The tilt ratio `κ_*` is nonnegative. -/
theorem kappaStar_nonneg : 0 ≤ kappaStar := kappaStar_pos.le

/-- The tilt ratio `κ_*` is less than `1`. -/
theorem kappaStar_lt_one : kappaStar < 1 := by
  rw [kappaStar_def]; norm_num

end CollatzPosDens
