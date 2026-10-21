/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02ScheduleMono

/-!
# The schedule positions strictly increase up to `rStar`

For a Fourier index `ι : FIndex`, the schedule positions `schedule ι i` strictly increase in `i`
as long as `i ≤ rStar ι`: chaining the one-step inequalities
`schedule_lt_schedule_succ_of_lt_rStar` gives `schedule ι i < schedule ι i'` whenever
`i < i' ≤ rStar ι`.

## Main results

* `CollatzPosDens.schedule_le_schedule`: for `i < i' ≤ rStar ι`,
  `schedule ι i < schedule ι i'`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The schedule positions strictly increase up to `rStar ι`: for `i < i' ≤ rStar ι`,
`schedule ι i < schedule ι i'`. -/
@[collatz_pos_dens "lem_tr_recipe_iter_mono"]
theorem schedule_le_schedule (ι : FIndex) {i i' : ℕ} (h : i < i') (hi' : i' ≤ rStar ι) :
    schedule ι i < schedule ι i' := by
  induction i', h using Nat.le_induction with
  | base => exact schedule_lt_schedule_succ_of_lt_rStar ι i (by omega)
  | succ n hn ih =>
    exact (ih (by omega)).trans (schedule_lt_schedule_succ_of_lt_rStar ι n (by omega))

end CollatzPosDens
