/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum

/-!
# The rational angle `v∘`

This file defines the rational number `v∘ = 6283 / 54250`, a fixed rational point below the
angle `8π / 217`. Since `6283 / 54250 = (6283 / 2000) · (8 / 217)` and `6283 / 2000 < π`,
this point lies strictly between `0` and `8π / 217`; being rational, every polynomial
inequality in `v∘` is decided by exact rational arithmetic.

## Main definitions

* `CollatzPosDens.chV0`: the rational number `v∘ = 6283 / 54250`.

## Main results

* `CollatzPosDens.chV0_pos`: `0 < v∘`.

## Implementation notes

`v∘` is a concrete element of `ℚ`, cast to `ℝ` where needed. The definition is exposed, so
`norm_num [chV0]` evaluates expressions in it.
-/

@[expose] public section

namespace CollatzPosDens

/-- The rational angle `v∘ = 6283 / 54250`. -/
@[collatz_pos_dens "def_ch_v0"]
def chV0 : ℚ := 6283 / 54250

/-- The angle `v∘` equals `6283 / 54250`. -/
theorem chV0_def : chV0 = 6283 / 54250 := rfl

/-- The angle `v∘` is positive. -/
theorem chV0_pos : 0 < chV0 := by
  norm_num [chV0]

end CollatzPosDens
