/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.TailMargin
public import CollatzPosDens.Recipe.ZMargin

/-!
# The seed margin

The tail margin `tailMargin` and the central-sum margin `centralSumMargin` together stay below
`13/15`. With `tailMargin = 6/7` and `centralSumMargin = 2^{-28}` this is the exact rational
comparison `13/15 - 6/7 = 1/105 > 2^{-28}`.

## Main results

* `CollatzPosDens.tailMargin_add_centralSumMargin_lt`: `tailMargin + centralSumMargin < 13/15`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The sum of the tail margin and the central-sum margin is less than `13/15`. -/
@[collatz_pos_dens "lem_seed_margin"]
theorem tailMargin_add_centralSumMargin_lt : tailMargin + centralSumMargin < 13 / 15 := by
  rw [tailMargin_def, centralSumMargin_def]
  norm_num

end CollatzPosDens
