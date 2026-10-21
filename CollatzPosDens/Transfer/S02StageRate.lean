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
# The stopped-stage mass `b_*`

The stopped-stage mass is the rational constant `b_* = 333407/10⁶`. It lies strictly between
`(77/100)⁵` and `(77/100)⁴`; in particular `max(b_*, (77/100)⁵) = b_*`, so five factors of
`77/100` have product dominated by `b_*`.

## Main definitions

* `CollatzPosDens.stageRate`: the stopped-stage mass `b_* = 333407/10⁶ : ℚ`.

## Main results

* `CollatzPosDens.stageRate_eq`, `CollatzPosDens.stageRate_cast`: the value `b_* = 333407/10⁶`.
* `CollatzPosDens.stageRate_pos`, `CollatzPosDens.stageRate_lt_one`: `0 < b_* < 1`.
* `CollatzPosDens.pow_five_lt_stageRate`, `CollatzPosDens.stageRate_lt_pow_four`:
  `(77/100)⁵ < b_* < (77/100)⁴`.
* `CollatzPosDens.max_stageRate_pow_five`: `max(b_*, (77/100)⁵) = b_*`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The stopped-stage mass `b_* := 333407/10⁶ ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_bstar"]
def stageRate : ℚ := 333407 / 10 ^ 6

/-- The value of the stopped-stage mass. -/
@[simp]
theorem stageRate_eq : stageRate = 333407 / 10 ^ 6 := rfl

/-- The value of the stopped-stage mass cast into a division ring of characteristic zero. -/
theorem stageRate_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (stageRate : K) = 333407 / 10 ^ 6 := by
  have h : stageRate = 333407 / 1000000 := by norm_num
  rw [h]
  norm_num

/-- The stopped-stage mass is positive. -/
theorem stageRate_pos : 0 < stageRate := by norm_num

/-- The stopped-stage mass is nonnegative. -/
theorem stageRate_nonneg : 0 ≤ stageRate := stageRate_pos.le

/-- The stopped-stage mass is less than one. -/
theorem stageRate_lt_one : stageRate < 1 := by norm_num

/-- Five entry steps of rate `77/100` have mass below the stopped-stage mass:
`(77/100)⁵ < b_*`. -/
theorem pow_five_lt_stageRate : (77 / 100 : ℚ) ^ 5 < stageRate := by norm_num

/-- The stopped-stage mass is below the mass of four entry steps of rate `77/100`:
`b_* < (77/100)⁴`. -/
theorem stageRate_lt_pow_four : stageRate < (77 / 100 : ℚ) ^ 4 := by norm_num

/-- The stage rate `max(b_*, (77/100)⁵)` is the stopped-stage mass `b_*`. -/
theorem max_stageRate_pow_five : max stageRate ((77 / 100 : ℚ) ^ 5) = stageRate :=
  max_eq_left pow_five_lt_stageRate.le

end CollatzPosDens
