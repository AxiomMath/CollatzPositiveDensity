/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.S02HSchedule

/-!
# The recipe map moves along the schedule

The schedule positions are the iterates of the recipe map: for every Fourier index `ι` and every
`0 ≤ i < r_*(ι)`, `𝔤_ι(p_i(ι)) = p_{i+1}(ι)`. Indeed (suppressing `ι`), at a schedule position
the window length is `h_*(p_i) = ⌈α_sc K_{*,i} (p_i + 1)⌉ + H_*`
(`CollatzPosDens.windowLength_schedule`), where `α_sc` is the slope of the trace schedule, so the
recipe map `𝔤(p_i) = p_i + h_*(p_i) + T_* + 1` is exactly the defining recurrence of `p_{i+1}`.

## Main results

* `CollatzPosDens.traceIndex_schedule`: `i_*(ι, p_i(ι)) = i` for `i ≤ r_*(ι)`.
* `CollatzPosDens.betaStar_schedule`: `β_*(ι, p_i(ι)) = S_i(ι)` for `i ≤ r_*(ι)`.
* `CollatzPosDens.recipeMap_schedule`: `𝔤_ι(p_i(ι)) = p_{i+1}(ι)` for `i < r_*(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The trace index of a schedule position is its index: `i_*(ι, p_i(ι)) = i` for
`i ≤ r_*(ι)`. -/
theorem traceIndex_schedule (ι : FIndex) {i : ℕ} (hi : i ≤ rStar ι) :
    traceIndex ι (schedule ι i) = i :=
  (traceIndex_eq_iff ι (schedule_monotone ι hi)).2
    ⟨hi, le_rfl, fun _ hj => schedule_strictMono ι hj⟩

/-- At a schedule position the oversize threshold is the interval size:
`β_*(ι, p_i(ι)) = S_i(ι)` for `i ≤ r_*(ι)`. -/
theorem betaStar_schedule (ι : FIndex) {i : ℕ} (hi : i ≤ rStar ι) :
    betaStar ι (schedule ι i) = sStar ι i := by
  rw [betaStar_def, traceIndex_schedule ι hi]

/-- The recipe map moves along the schedule: for every index `ι`,
`𝔤_ι(p_i(ι)) = p_{i+1}(ι)` for every `0 ≤ i < r_*(ι)`. -/
@[collatz_pos_dens "lem_s02_g_schedule"]
theorem recipeMap_schedule (ι : FIndex) :
    ∀ i < rStar ι, recipeMap ι (schedule ι i) = schedule ι (i + 1) := by
  intro i hi
  rw [recipeMap_def, windowLength_schedule_eq_div ι hi.le, sStar_def, schedule_succ_eq_div,
    ← mul_assoc]
  ring

end CollatzPosDens
