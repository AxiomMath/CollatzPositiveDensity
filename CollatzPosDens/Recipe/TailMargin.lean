/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# The tail margin `θ_tl`

This file defines the tail margin, the rational number `θ_tl := 6/7`.

## Main definitions

* `CollatzPosDens.tailMargin`: the tail margin `θ_tl := 6/7`.

## Main results

* `CollatzPosDens.tailMargin_def`: `θ_tl = 6/7`.
* `CollatzPosDens.tailMargin_cast`: `(θ_tl : ℝ) = 6/7`.

## Implementation notes

The margin is reducible, so `push_cast` and `norm_num` see its value.
-/

@[expose] public section

namespace CollatzPosDens

/-- The tail margin `θ_tl := 6/7 ∈ ℚ`. -/
@[collatz_pos_dens "def_tail_margin"]
abbrev tailMargin : ℚ := 6 / 7

/-- The value of the tail margin. -/
theorem tailMargin_def : tailMargin = 6 / 7 := rfl

/-- The real value of the tail margin. -/
theorem tailMargin_cast : (tailMargin : ℝ) = 6 / 7 := by
  norm_num [tailMargin]

end CollatzPosDens
