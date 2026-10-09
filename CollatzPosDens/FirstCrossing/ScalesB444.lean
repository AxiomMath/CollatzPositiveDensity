/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales

/-!
# The scale `b_444 = 16544`

The scales `b_j` are given by `b_0 = 9` and `b_{j+1} = b_j + e_{b_j}`. Evaluating this
recursion exactly, with each increment `e_{b_j}` computed from its definition, gives
`b_444 = 16544`.

## Main results

* `CollatzPosDens.scale_444`: `b_444 = 16544`.

## Implementation notes

Both `scale` and `eb` are computable natural-number functions with decidable branches, so the
value is obtained by kernel evaluation of the recursion on numerals.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale `b_444` equals `16544`. -/
@[collatz_pos_dens "lem_scales_b444"]
theorem scale_444 : scale 444 = 16544 := by
  decide +kernel

end CollatzPosDens
