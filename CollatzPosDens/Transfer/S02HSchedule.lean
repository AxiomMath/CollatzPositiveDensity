/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02HDef
public import CollatzPosDens.Transfer.S02ScheduleMono
public import CollatzPosDens.Transfer.S02ScheduleValues

/-!
# The window length along the schedule

At a schedule position the window length is given by the interval size of that position: for
every Fourier index `ι` and every `0 ≤ i ≤ r_*(ι)`,
$$h_*(ι, p_i(ι)) = \lceil α_{\mathrm{sc}}(ι)\,\mathsf S_i(ι)\rceil + H_*(ι),$$
where `α_sc(ι)` is the slope of the trace schedule. Indeed (suppressing `ι`), since the schedule
is strictly increasing, `p_i` is the first schedule position that is at least `p_i`, so the trace
index of `p_i` is `i`; hence `β_*(p_i) = S_i`, and the formula is the definition of `h_*`.

At the bootstrap index, with `p(b) = (169, 15486, 514217, 63701994)` and
`K_*(b) = (718, 268, 1024, 2^30)`, the interval sizes are
`S(b) = (122060, 4150516, 526559232, 68399496303738880)`, and, as `α_sc(b) = 3/25` and
`H_*(b) = 500`, the window lengths at the schedule positions are
`h_*(b, p_i(b)) = (15148, 498562, 63187608, 8207939556449166)`.

## Main results

* `CollatzPosDens.windowLength_schedule`: `h_*(p_i) = ⌈α_sc S_i⌉ + H_*` for `i ≤ r_*`.
* `CollatzPosDens.windowLength_schedule_eq_div`: the same with the ceiling as a natural-number
  division, `h_*(p_i) = (a S_i + d - 1) / d + H_*`, where `α_sc = a / d`.
* `CollatzPosDens.sStar_values_b`: the list `[S_0(b), …, S_3(b)]`.
* `CollatzPosDens.windowLength_schedule_values_b`: the list `[h_*(b, p_0(b)), …, h_*(b, p_3(b))]`.
-/

@[expose] public section

namespace CollatzPosDens

/-- At a schedule position the oversize threshold is the interval size: `β_*(p_i) = S_i` for
`i ≤ r_*`. -/
private theorem betaStar_schedule_aux (ι : FIndex) {i : ℕ} (hi : i ≤ rStar ι) :
    betaStar ι (schedule ι i) = sStar ι i := by
  have hidx : traceIndex ι (schedule ι i) = i :=
    (traceIndex_eq_iff ι (schedule_monotone ι hi)).2
      ⟨hi, le_rfl, fun j hj => by
        induction i, hj using Nat.le_induction with
        | base => exact schedule_lt_schedule_succ_of_lt_rStar ι j (by omega)
        | succ k hjk ih =>
          exact (ih (by omega)).trans (schedule_lt_schedule_succ_of_lt_rStar ι k (by omega))⟩
  rw [betaStar_def, hidx]

/-- The window length at a schedule position: for every index `ι` and every
`0 ≤ i ≤ r_*(ι)`, `h_*(ι, p_i(ι)) = ⌈α_sc(ι) S_i(ι)⌉ + H_*(ι)`. -/
@[collatz_pos_dens "lem_s02_h_schedule"]
theorem windowLength_schedule (ι : FIndex) {i : ℕ} (hi : i ≤ rStar ι) :
    windowLength ι (schedule ι i) = ⌈(traceSlope ι : ℝ) * sStar ι i⌉₊ + Hstar ι := by
  rw [windowLength_def, betaStar_schedule_aux ι hi]

/-- The window length at a schedule position, with the ceiling as a natural-number division:
writing `α_sc(ι) = a / d`, `h_*(ι, p_i(ι)) = (a S_i(ι) + d - 1) / d + H_*(ι)` for every
`0 ≤ i ≤ r_*(ι)`. -/
theorem windowLength_schedule_eq_div (ι : FIndex) {i : ℕ} (hi : i ≤ rStar ι) :
    windowLength ι (schedule ι i) =
      (traceSlopeNum ι * sStar ι i + traceSlopeDen ι - 1) / traceSlopeDen ι + Hstar ι := by
  rw [windowLength_eq_div, betaStar_schedule_aux ι hi]

/-- The four schedule positions `p_0(b), …, p_3(b)` at the bootstrap index. -/
private lemma sStar_values_b_schedule :
    schedule .b 0 = 169 ∧ schedule .b 1 = 15486 ∧ schedule .b 2 = 514217 ∧
      schedule .b 3 = 63701994 := by
  have h := schedule_values_b
  simp only [rStar_b, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The four interval sizes `S_0(b), …, S_3(b)` at the bootstrap index. -/
theorem sStar_values_b :
    List.ofFn (fun i : Fin (rStar .b + 1) => sStar .b i) =
      [122060, 4150516, 526559232, 68399496303738880] := by
  obtain ⟨h0, h1, h2, h3⟩ := sStar_values_b_schedule
  have e0 : sStar .b 0 = 122060 := by rw [sStar_def, h0, Kstar_b_zero]
  have e1 : sStar .b 1 = 4150516 := by rw [sStar_def, h1, Kstar_b_one]
  have e2 : sStar .b 2 = 526559232 := by rw [sStar_def, h2, Kstar_b_two]
  have e3 : sStar .b 3 = 68399496303738880 := by
    rw [sStar_def, h3, Kstar_b_of_three_le le_rfl]
    norm_num
  simp [List.ofFn_succ, e0, e1, e2, e3]

/-- The four window lengths `h_*(b, p_0(b)), …, h_*(b, p_3(b))` at the bootstrap schedule
positions. -/
theorem windowLength_schedule_values_b :
    List.ofFn (fun i : Fin (rStar .b + 1) => windowLength .b (schedule .b i)) =
      [15148, 498562, 63187608, 8207939556449166] := by
  have hS := sStar_values_b
  simp only [rStar_b, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    List.cons.injEq] at hS
  obtain ⟨h0, h1, h2, h3, -⟩ := hS
  have e : ∀ i : ℕ, i ≤ 3 → ∀ s : ℕ, sStar .b i = s →
      windowLength .b (schedule .b i) = (3 * s + 24) / 25 + 500 := by
    intro i hi s hs
    rw [windowLength_schedule_eq_div .b hi, hs, traceSlopeNum_b, traceSlopeDen_b, Hstar_b]
    omega
  simp [List.ofFn_succ, -schedule_zero, e 0 (by decide) _ h0, e 1 (by decide) _ h1,
    e 2 (by decide) _ h2, e 3 (by decide) _ h3]

end CollatzPosDens
