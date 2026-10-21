/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageTimes
public import CollatzPosDens.Transfer.S02ScheduleValues
public import CollatzPosDens.Transfer.S02HSchedule
public import CollatzPosDens.Transfer.S02TraceIndex

/-!
# The stage deadlines of the bootstrap set

At the bootstrap index `b`, with gap threshold `G = 4096` and run length `d = 5`, the first
three stage deadlines are
```
(𝔱^{4096,5}_0(b), 𝔱^{4096,5}_1(b), 𝔱^{4096,5}_2(b)) = (169, 503672, 63696221).
```
The clearance time is `h^st_4096(b) = 1024 + 168 + 1 = 1193`, and the schedule positions are
`(p_0(b), p_1(b), p_2(b), p_3(b)) = (169, 15486, 514217, 63701994)`, with interval sizes
`S_1(b) = 268 · 15487 = 4150516` and `S_2(b) = 1024 · 514218 = 526559232`. First
`𝔱_0 = p_0(b) = 169`. Next `𝔱_1 = max(169 + 5 · 1193, 𝔤_b(169 + 4 · 1193)) =
max(6134, 𝔤_b(4941))`; as `p_0(b) < 4941 ≤ p_1(b)`, the trace index of `4941` is `1`, so
`h_*(b, 4941) = ⌈(3/25) · 4150516⌉ + 500 = 498562` and `𝔤_b(4941) = 4941 + 498562 + 169 =
503672`. Finally `𝔱_2 = max(503672 + 5965, 𝔤_b(503672 + 4772)) = max(509637, 𝔤_b(508444))`;
as `p_1(b) < 508444 ≤ p_2(b)`, the trace index of `508444` is `2`, so
`h_*(b, 508444) = ⌈(3/25) · 526559232⌉ + 500 = 63187608` and
`𝔤_b(508444) = 508444 + 63187608 + 169 = 63696221 > 509637`.

## Main results

* `CollatzPosDens.trStageTime_b_values`: the three deadlines `(169, 503672, 63696221)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The schedule positions `p_0(b), …, p_3(b) = 169, 15486, 514217, 63701994`. -/
private theorem schedule_b_values_stageTimes :
    schedule .b 0 = 169 ∧ schedule .b 1 = 15486 ∧ schedule .b 2 = 514217 ∧
      schedule .b 3 = 63701994 := by
  have h := schedule_values_b
  simp only [rStar_b, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The interval sizes `S_1(b) = 4150516` and `S_2(b) = 526559232`. -/
private theorem sStar_b_values_stageTimes :
    sStar .b 1 = 4150516 ∧ sStar .b 2 = 526559232 := by
  have h := sStar_values_b
  simp only [rStar_b, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    List.cons.injEq] at h
  exact ⟨h.2.1, h.2.2.1⟩

/-- `𝔤_b(4941) = 503672`, the trace index of `4941` being `1`. -/
private theorem recipeMap_b_4941 : recipeMap .b 4941 = 503672 := by
  obtain ⟨h0, h1, -, h3⟩ := schedule_b_values_stageTimes
  have hidx : traceIndex .b 4941 = 1 := by
    rw [traceIndex_eq_iff .b (by rw [rStar_b, h3]; norm_num)]
    refine ⟨by rw [rStar_b]; norm_num, by rw [h1]; norm_num, fun j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    rw [h0]; norm_num
  rw [recipeMap_b_eq, windowLength_b_eq_div, betaStar_def, hidx,
    sStar_b_values_stageTimes.1]

/-- `𝔤_b(508444) = 63696221`, the trace index of `508444` being `2`. -/
private theorem recipeMap_b_508444 : recipeMap .b 508444 = 63696221 := by
  obtain ⟨h0, h1, h2, h3⟩ := schedule_b_values_stageTimes
  have hidx : traceIndex .b 508444 = 2 := by
    rw [traceIndex_eq_iff .b (by rw [rStar_b, h3]; norm_num)]
    refine ⟨by rw [rStar_b]; norm_num, by rw [h2]; norm_num, fun j hj => ?_⟩
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [h0]; norm_num
    · rw [h1]; norm_num
  rw [recipeMap_b_eq, windowLength_b_eq_div, betaStar_def, hidx,
    sStar_b_values_stageTimes.2]

/-- **The stage deadlines of the bootstrap set.**
`(𝔱^{4096,5}_0(b), 𝔱^{4096,5}_1(b), 𝔱^{4096,5}_2(b)) = (169, 503672, 63696221)`. -/
@[collatz_pos_dens "lem_c3_stage_times_b"]
theorem trStageTime_b_values :
    (trStageTime .b 4096 5 0, trStageTime .b 4096 5 1, trStageTime .b 4096 5 2) =
      (169, 503672, 63696221) := by
  have h0 : trStageTime .b 4096 5 0 = 169 := by
    rw [trStageTime_zero, schedule_b_values_stageTimes.1]
  have h1 : trStageTime .b 4096 5 1 = 503672 := by
    rw [trStageTime_succ, h0, trStageMap_def, trStageHold_b_4096,
      show 169 + (5 - 1) * 1193 = 4941 by norm_num, recipeMap_b_4941]
    norm_num
  have h2 : trStageTime .b 4096 5 2 = 63696221 := by
    rw [trStageTime_succ, h1, trStageMap_def, trStageHold_b_4096,
      show 503672 + (5 - 1) * 1193 = 508444 by norm_num, recipeMap_b_508444]
    norm_num
  rw [h0, h1, h2]

end CollatzPosDens
