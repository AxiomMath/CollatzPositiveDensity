/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.SelEnd

/-!
# The scale `scale selEnd = 22095`

The scales `scale j` are given by `scale 0 = 16544` and
`scale (j + 1) = scale j + ⌈scale j / 100⌉`. Evaluating the `29` steps from `16544` exactly in
integer arithmetic (the first two give `scale 1 = 16710` and `scale 2 = 16878`) gives
`scale selEnd = 22095`, where `selEnd = 29`.

## Main results

* `CollatzPosDens.scale_selEnd`: `scale selEnd = 22095`.

## Implementation notes

The value is checked by kernel evaluation of the natural-number recursion defining `scale`.
-/
@[expose] public section

namespace CollatzPosDens

/-- The scale at the index `selEnd` is `scale selEnd = 22095`. -/
@[collatz_pos_dens "lem_scales_b473"]
theorem scale_selEnd : scale selEnd = 22095 := by
  decide +kernel

end CollatzPosDens
