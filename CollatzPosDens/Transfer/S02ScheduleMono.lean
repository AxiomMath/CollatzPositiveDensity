/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Schedule
public import CollatzPosDens.Transfer.Rstar

/-!
# The schedule positions strictly increase

For every Fourier parameter index `ι ∈ {o, b}` the schedule positions satisfy
`p_i(ι) < p_{i+1}(ι)` for every `0 ≤ i < r_*(ι)`. Indeed the increment `p_{i+1}(ι) - p_i(ι)` is
the sum of the nonnegative ceiling `⌈α_sc(ι) K_{*,i}(ι) (p_i(ι) + 1)⌉`, where `α_sc(ι) > 0` is
the slope of the trace schedule, and of `H_*(ι) + T_*(ι) + 1 ≥ 1`.

## Main results

* `CollatzPosDens.schedule_lt_schedule_succ_of_lt_rStar`: `p_i(ι) < p_{i+1}(ι)` for every
  `i < r_*(ι)`.

## Implementation notes

The inequality holds for every `i : ℕ` (this is `CollatzPosDens.schedule_lt_schedule_succ`);
the statement here records it on the range `i < r_*(ι)` of schedule steps actually used.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The schedule positions strictly increase along the schedule: for every index `ι`,
`p_i(ι) < p_{i+1}(ι)` for every `0 ≤ i < r_*(ι)`. -/
@[collatz_pos_dens "lem_s02_schedule_mono"]
theorem schedule_lt_schedule_succ_of_lt_rStar (ι : FIndex) :
    ∀ i < rStar ι, schedule ι i < schedule ι (i + 1) :=
  fun i _ => schedule_lt_schedule_succ ι i

end CollatzPosDens
