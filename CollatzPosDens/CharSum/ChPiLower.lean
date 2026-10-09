/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A rational lower bound for `π`

This file proves the numerical bound `π > 6283 / 2000 = 3.1415`.

## Main results

* `CollatzPosDens.pi_gt_6283_div_2000`: `6283 / 2000 < π`.

## Implementation notes

The bound can be derived from the Machin-type identity `π / 4 = arctan (1/2) + arctan (1/3)`
and truncated alternating arctangent series. We instead deduce it from the decimal bound
`3.1415 < π` (`Real.pi_gt_d4`), since `6283 / 2000 = 3.1415` exactly.
-/

@[expose] public section

namespace CollatzPosDens

/-- `π > 6283 / 2000`. -/
@[collatz_pos_dens "lem_ch_pi_lower"]
theorem pi_gt_6283_div_2000 : (6283 / 2000 : ℝ) < Real.pi := by
  have := Real.pi_gt_d4
  norm_num at this ⊢
  linarith

end CollatzPosDens
