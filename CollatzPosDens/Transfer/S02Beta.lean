/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02S
public import CollatzPosDens.Transfer.S02SMono
public import CollatzPosDens.Transfer.S02TraceIndex

/-!
# The oversize threshold `β_*`

For a Fourier index `ι` and a time `u ∈ ℕ` the oversize threshold is the natural number
`β_*(ι, u) := S_{i_*(ι, u)}(ι)`, the interval size `S_i(ι) = K_{*,i}(ι) (p_i(ι) + 1)` at the trace
index `i_*(ι, u) ∈ {0, …, r_*(ι)}`: a triangle visited at time `u` is oversize when its size is
at least `β_*(ι, u)`. As a function of `u` (with `ι` fixed and suppressed) it is a step function,
constant on each block `p_{i-1} < u ≤ p_i` of the schedule, and equal to `S_{r_*}` for
`u > p_{r_*}`.

## Main definitions

* `CollatzPosDens.betaStar`: the oversize threshold `β_*(ι, u) = S_{i_*(ι, u)}(ι)`.

## Main results

* `CollatzPosDens.betaStar_pos`: `0 < β_*(u)`.
* `CollatzPosDens.sStar_le_sStar_of_le`: `S_i ≤ S_j` for `i ≤ j ≤ r_*`.
* `CollatzPosDens.traceIndex_monotone`: `i_*` is monotone.
* `CollatzPosDens.betaStar_monotone`: `β_*` is monotone.
-/

@[expose] public section

namespace CollatzPosDens

/-- The oversize threshold `β_*(ι, u) := S_{i_*(ι, u)}(ι) ∈ ℕ`, the interval size `sStar` at the
trace index `traceIndex ι u`. -/
@[collatz_pos_dens "def_s02_beta"]
def betaStar (ι : FIndex) (u : ℕ) : ℕ := sStar ι (traceIndex ι u)

/-- The defining formula `β_*(ι, u) = S_{i_*(ι, u)}(ι)`. -/
theorem betaStar_def (ι : FIndex) (u : ℕ) : betaStar ι u = sStar ι (traceIndex ι u) := rfl

/-- The oversize threshold is positive: `0 < β_*(ι, u)` for every `u ∈ ℕ`. -/
theorem betaStar_pos (ι : FIndex) (u : ℕ) : 0 < betaStar ι u := sStar_pos ι _

/-- Beyond the last schedule position, `β_*(ι, u) = S_{r_*(ι)}(ι)`. -/
theorem betaStar_of_schedule_lt (ι : FIndex) {u : ℕ} (hu : schedule ι (rStar ι) < u) :
    betaStar ι u = sStar ι (rStar ι) := by
  rw [betaStar_def, traceIndex_of_schedule_lt ι hu]

/-- The interval sizes are nondecreasing on the schedule: `S_i(ι) ≤ S_j(ι)` for
`i ≤ j ≤ r_*(ι)`. -/
theorem sStar_le_sStar_of_le (ι : FIndex) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ rStar ι) :
    sStar ι i ≤ sStar ι j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (sStar_le_sStar_succ ι (by omega))

/-- The trace index is monotone: `i_*(ι, u) ≤ i_*(ι, u')` whenever `u ≤ u'`. -/
theorem traceIndex_monotone (ι : FIndex) : Monotone (traceIndex ι) := by
  intro u u' huu'
  rcases le_or_gt u' (schedule ι (rStar ι)) with hu' | hu'
  · exact (traceIndex_le_iff ι (huu'.trans hu')).2 (huu'.trans (le_schedule_traceIndex ι hu'))
  · rw [traceIndex_of_schedule_lt ι hu']
    exact traceIndex_le_rStar ι u

/-- The oversize threshold is monotone: for every index `ι`, `β_*(ι, u) ≤ β_*(ι, u')` whenever
`u ≤ u'`. -/
@[collatz_pos_dens "lem_s02_beta_mono"]
theorem betaStar_monotone (ι : FIndex) : Monotone (betaStar ι) := fun _ _ h =>
  sStar_le_sStar_of_le ι (traceIndex_monotone ι h) (traceIndex_le_rStar ι _)

end CollatzPosDens
