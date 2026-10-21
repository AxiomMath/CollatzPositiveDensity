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
# The central-sum margin `ε_Z`

This file defines the central-sum margin, the rational number `ε_Z := 2^{-28}`, and records its
value, its real cast and its positivity.

## Main definitions

* `CollatzPosDens.centralSumMargin`: the margin `ε_Z := 2^{-28}`.

## Main results

* `CollatzPosDens.centralSumMargin_def`: `ε_Z = 2^{-28}`.
* `CollatzPosDens.centralSumMargin_cast`: `(ε_Z : ℝ) = 2^{-28}`.
* `CollatzPosDens.centralSumMargin_pos`: `0 < ε_Z`.

## Implementation notes

The margin is reducible, so `push_cast` and `norm_num` see its value.
-/

@[expose] public section

namespace CollatzPosDens

/-- The central-sum margin `ε_Z := 2^{-28} ∈ ℚ`. -/
@[collatz_pos_dens "def_Z_margin"]
abbrev centralSumMargin : ℚ := 2⁻¹ ^ 28

/-- The value of the central-sum margin. -/
theorem centralSumMargin_def : centralSumMargin = 2⁻¹ ^ 28 := rfl

/-- The real value of the central-sum margin. -/
theorem centralSumMargin_cast : (centralSumMargin : ℝ) = (2 : ℝ)⁻¹ ^ 28 := by
  norm_num [centralSumMargin]

/-- The central-sum margin is positive. -/
theorem centralSumMargin_pos : 0 < centralSumMargin := by
  norm_num [centralSumMargin]

end CollatzPosDens
