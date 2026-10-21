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
# The target exponent `κ_t`

This file defines the target exponent `κ_t := 25/11`, the rational exponent to which the target
`t` is raised in the density constant of the positive-density estimate.

## Main definitions

* `CollatzPosDens.targetExp`: the target exponent `κ_t := 25/11`.

## Main results

* `CollatzPosDens.targetExp_def`: `κ_t = 25/11`.
* `CollatzPosDens.targetExp_cast`: `(κ_t : ℝ) = 25/11`.
* `CollatzPosDens.targetExp_pos`: `0 < κ_t`.

## Implementation notes

The exponent is reducible, so `push_cast` and `norm_num` see its value.
-/

@[expose] public section

namespace CollatzPosDens

/-- The target exponent `κ_t := 25/11 ∈ ℚ`, the exponent of the target in the density
constant. -/
@[collatz_pos_dens "def_target_exp"]
abbrev targetExp : ℚ := 25 / 11

/-- The value of the target exponent. -/
theorem targetExp_def : targetExp = 25 / 11 := rfl

/-- The real value of the target exponent. -/
theorem targetExp_cast : (targetExp : ℝ) = 25 / 11 := by
  norm_num [targetExp]

/-- The target exponent is positive. -/
theorem targetExp_pos : 0 < targetExp := by
  norm_num [targetExp]

end CollatzPosDens
