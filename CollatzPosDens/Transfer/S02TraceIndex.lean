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
# The trace index `i_*(u)`

For a Fourier index `ι` and a time `u ∈ ℕ`, the trace index `i_*(ι, u)` is the first schedule
index `i ∈ {0, …, r_*(ι)}` with `u ≤ p_i(ι)`, when such an index exists (that is, when
`u ≤ p_{r_*(ι)}(ι)`), and `r_*(ι)` otherwise. Here `p_i(ι)` is `CollatzPosDens.schedule ι i`
and `r_*(ι)` is `CollatzPosDens.rStar ι`. Throughout, `ι` is fixed and suppressed from the
notation.

## Main definitions

* `CollatzPosDens.traceIndex`: the trace index `i_*(ι, u)`.

## Main results

* `CollatzPosDens.traceIndex_le_rStar`: `i_*(u) ≤ r_*`.
* `CollatzPosDens.le_schedule_traceIndex`: if `u ≤ p_{r_*}` then `u ≤ p_{i_*(u)}`.
* `CollatzPosDens.schedule_lt_of_lt_traceIndex`: if `j < i_*(u)` then `p_j < u`.
* `CollatzPosDens.traceIndex_of_schedule_lt`: if `p_{r_*} < u` then `i_*(u) = r_*`.
* `CollatzPosDens.traceIndex_le_iff`: if `u ≤ p_{r_*}` then `i_*(u) ≤ i ↔ u ≤ p_i`.
* `CollatzPosDens.traceIndex_eq_iff`: for `u ≤ p_{r_*}`, `i_*(u) = i` iff `i` is the first index
  with `u ≤ p_i`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The trace index: `i_*(ι, u) := min {i ∈ {0, …, r_*(ι)} : u ≤ p_i(ι)}` if
`u ≤ p_{r_*(ι)}(ι)`, and `i_*(ι, u) := r_*(ι)` if `u > p_{r_*(ι)}(ι)`. -/
@[collatz_pos_dens "def_s02_trace_index"]
def traceIndex (ι : FIndex) (u : ℕ) : ℕ :=
  if h : ∃ i, i ≤ rStar ι ∧ u ≤ schedule ι i then Nat.find h else rStar ι

/-- The existence condition in `traceIndex` holds exactly when `u ≤ p_{r_*}`. -/
theorem exists_le_rStar_le_schedule_iff (ι : FIndex) (u : ℕ) :
    (∃ i, i ≤ rStar ι ∧ u ≤ schedule ι i) ↔ u ≤ schedule ι (rStar ι) :=
  ⟨fun ⟨_, hi, hu⟩ => hu.trans (schedule_monotone ι hi), fun h => ⟨rStar ι, le_rfl, h⟩⟩

/-- If `u ≤ p_{r_*}`, the trace index is the least `i` with `i ≤ r_*` and `u ≤ p_i`. -/
theorem traceIndex_of_le (ι : FIndex) {u : ℕ} (hu : u ≤ schedule ι (rStar ι)) :
    traceIndex ι u = Nat.find ((exists_le_rStar_le_schedule_iff ι u).2 hu) := by
  unfold traceIndex
  split_ifs with h
  · rfl
  · exact absurd ((exists_le_rStar_le_schedule_iff ι u).2 hu) h

/-- If `p_{r_*} < u` then `i_*(u) = r_*`. -/
theorem traceIndex_of_schedule_lt (ι : FIndex) {u : ℕ} (hu : schedule ι (rStar ι) < u) :
    traceIndex ι u = rStar ι := by
  unfold traceIndex
  split_ifs with h
  · exact absurd ((exists_le_rStar_le_schedule_iff ι u).1 h) (not_le.2 hu)
  · rfl

/-- The trace index is at most `r_*`. -/
theorem traceIndex_le_rStar (ι : FIndex) (u : ℕ) : traceIndex ι u ≤ rStar ι := by
  rcases le_or_gt u (schedule ι (rStar ι)) with hu | hu
  · rw [traceIndex_of_le ι hu]
    exact (Nat.find_spec ((exists_le_rStar_le_schedule_iff ι u).2 hu)).1
  · rw [traceIndex_of_schedule_lt ι hu]

/-- If `u ≤ p_{r_*}` then `u ≤ p_{i_*(u)}`. -/
theorem le_schedule_traceIndex (ι : FIndex) {u : ℕ} (hu : u ≤ schedule ι (rStar ι)) :
    u ≤ schedule ι (traceIndex ι u) := by
  rw [traceIndex_of_le ι hu]
  exact (Nat.find_spec ((exists_le_rStar_le_schedule_iff ι u).2 hu)).2

/-- Every schedule index below the trace index has `p_j < u`. -/
theorem schedule_lt_of_lt_traceIndex (ι : FIndex) {u j : ℕ} (hj : j < traceIndex ι u) :
    schedule ι j < u := by
  rcases le_or_gt u (schedule ι (rStar ι)) with hu | hu
  · rw [traceIndex_of_le ι hu] at hj
    have := Nat.find_min _ hj
    have hjr : j ≤ rStar ι :=
      hj.le.trans (Nat.find_spec ((exists_le_rStar_le_schedule_iff ι u).2 hu)).1
    simp only [not_and, not_le] at this
    exact this hjr
  · rw [traceIndex_of_schedule_lt ι hu] at hj
    exact (schedule_monotone ι hj.le).trans_lt hu

/-- For `u ≤ p_{r_*}`, `i_*(u) = i` iff `u ≤ p_i`, `i ≤ r_*`, and `p_j < u` for all `j < i`. -/
theorem traceIndex_eq_iff (ι : FIndex) {u i : ℕ} (hu : u ≤ schedule ι (rStar ι)) :
    traceIndex ι u = i ↔ i ≤ rStar ι ∧ u ≤ schedule ι i ∧ ∀ j < i, schedule ι j < u := by
  constructor
  · rintro rfl
    exact ⟨traceIndex_le_rStar ι u, le_schedule_traceIndex ι hu,
      fun _ hj => schedule_lt_of_lt_traceIndex ι hj⟩
  · rintro ⟨hi, hui, hlt⟩
    rw [traceIndex_of_le ι hu, Nat.find_eq_iff]
    refine ⟨⟨hi, hui⟩, fun j hj ⟨_, h⟩ => ?_⟩
    exact absurd h (not_le.2 (hlt j hj))

/-- For `u ≤ p_{r_*}`, `i_*(u)` is the least index `i` with `u ≤ p_i`:
`i_*(u) ≤ i ↔ u ≤ p_i`. -/
theorem traceIndex_le_iff (ι : FIndex) {u i : ℕ} (hu : u ≤ schedule ι (rStar ι)) :
    traceIndex ι u ≤ i ↔ u ≤ schedule ι i := by
  constructor
  · intro h
    exact (le_schedule_traceIndex ι hu).trans (schedule_monotone ι h)
  · intro h
    by_contra hlt
    exact absurd h (not_le.2 (schedule_lt_of_lt_traceIndex ι (not_le.1 hlt)))

end CollatzPosDens
