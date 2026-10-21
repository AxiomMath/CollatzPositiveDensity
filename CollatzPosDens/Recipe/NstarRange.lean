/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.SelEnd
public import CollatzPosDens.Recipe.CovGen
public import CollatzPosDens.Recipe.Nstar

/-!
# The position of the generation threshold

The generation threshold lies between the end of the offset selector and the coverage generation:
`selEnd ≤ generationThreshold ≤ covGen`, that is `29 ≤ 9853 ≤ 23000`.

## Main results

* `CollatzPosDens.selEnd_le_generationThreshold_range`: `selEnd ≤ generationThreshold` and
  `generationThreshold ≤ covGen`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The end of the offset selector is at most the generation threshold, which is at most the
coverage generation: `selEnd ≤ generationThreshold ≤ covGen`. -/
@[collatz_pos_dens "lem_Nstar_range"]
theorem selEnd_le_generationThreshold_range :
    selEnd ≤ generationThreshold ∧ generationThreshold ≤ covGen := by
  rw [selEnd_eq, generationThreshold_def, covGen_def]
  decide

end CollatzPosDens
