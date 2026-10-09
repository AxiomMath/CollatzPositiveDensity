/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.Schedule

/-!
# The schedule positions increase

The schedule positions are `schedule i = recipeMap^[i] pInit`. Since `q < recipeMap q` for every
`q : ℕ` (`lt_recipeMap`), we have `schedule i < schedule (i + 1)`, and hence
`schedule i ≤ schedule i'` whenever `i ≤ i'`.

## Main results

* `CollatzPosDens.schedule_le_schedule`: for `i ≤ i'`, `schedule i ≤ schedule i'`.

## Implementation notes

The statement is `schedule_monotone` applied to `i ≤ i'`; that monotonicity follows from
`schedule_strictMono`, which rests on the inflationary bound `lt_recipeMap`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The schedule positions increase: for `i ≤ i'`, `schedule i ≤ schedule i'`. -/
@[collatz_pos_dens "lem_tr_recipe_iter_mono"]
theorem schedule_le_schedule {i i' : ℕ} (h : i ≤ i') : schedule i ≤ schedule i' :=
  schedule_monotone h

end CollatzPosDens
