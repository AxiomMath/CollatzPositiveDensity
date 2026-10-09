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
# The continuation factor `c_cont`

The continuation factor is the positive rational constant `c_cont = 511/10`. This file records
its value, its cast into any division ring of characteristic zero, and the bounds
`0 < c_cont` and `1 < c_cont`.

## Main definitions

* `CollatzPosDens.ccont`: the continuation factor `c_cont = 511/10 : ℚ`.

## Main results

* `CollatzPosDens.ccont_eq`: the value `c_cont = 511/10`.
* `CollatzPosDens.ccont_cast`: the value of `(c_cont : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.ccont_pos`: `0 < c_cont`.
* `CollatzPosDens.one_lt_ccont`: `1 < c_cont`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The continuation factor `c_cont := 511/10 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_cont"]
def ccont : ℚ := 511 / 10

/-- The value of the continuation factor. -/
@[simp]
theorem ccont_eq : ccont = 511 / 10 := rfl

/-- The value of the continuation factor cast into a division ring of characteristic zero. -/
theorem ccont_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (ccont : K) = 511 / 10 := by
  simp [ccont_eq]

/-- The continuation factor is positive. -/
theorem ccont_pos : 0 < ccont := by norm_num

/-- The continuation factor exceeds one. -/
theorem one_lt_ccont : 1 < ccont := by norm_num

end CollatzPosDens
