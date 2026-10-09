/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.ScalesB42

/-!
# The scale `b_42`

The scales `b_j` satisfy `b_0 = 9` and `b_{j+1} = b_j + e_{b_j}`. Following the recursion
through the pairs `(b_j, e_{b_j})` for `0 ≤ j ≤ 41`, ending with `(233, 23)`, gives
`b_42 = 233 + 23 = 256`, the first scale at which the increment `e_b` takes its fallback
value `⌈b/100⌉`.

## Main results

* `CollatzPosDens.scale_forty_two`: `b_42 = 256`.

## Implementation notes

The value is computed in `CollatzPosDens.scale_42` by evaluating the recursion in the kernel;
`CollatzPosDens.scale_forty_two` restates that theorem.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale `b_42` equals `256`. -/
@[collatz_pos_dens "lem_ck_scale_42"]
theorem scale_forty_two : scale 42 = 256 := scale_42

end CollatzPosDens
