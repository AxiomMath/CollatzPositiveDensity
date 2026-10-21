/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Schedule

/-!
# The values of the schedule positions `p_i(ι)`

At the original index, `p_init(o) = 193`, `α_sc(o) = 113/1000`, `H_*(o) = 10100`,
`T_*(o) = 192` and `r_*(o) = 10`, so the schedule recurrence reads
`p_{i+1} = p_i + ⌈113 K_{*,i}(o) (p_i + 1) / 1000⌉ + 10293`, with an integer ceiling;
iterating it ten times from `p_0 = 193` gives the eleven positions `p_0(o), …, p_10(o)` exactly.
At the bootstrap index, `p_init(b) = 169`, `α_sc(b) = 3/25`,
`H_*(b) = 500`, `T_*(b) = 168` and `r_*(b) = 3`, so the recurrence reads
`p_{i+1} = p_i + ⌈3 K_{*,i}(b) (p_i + 1) / 25⌉ + 669`; iterating it three times from `p_0 = 169`
with `K_{*,0}(b), K_{*,1}(b), K_{*,2}(b) = 718, 268, 1024` gives the four positions
`p_0(b), …, p_3(b) = 169, 15486, 514217, 63701994` exactly.

## Main results

* `CollatzPosDens.schedule_values_o`: the list `[p_0(o), …, p_10(o)]`.
* `CollatzPosDens.schedule_values_b`: the list `[p_0(b), …, p_3(b)]`.

## Implementation notes

Each step uses the recurrence in the form
`p_{i+1} = p_i + (a K_{*,i} (p_i + 1) + d - 1) / d + H_* + T_* + 1`, where `α_sc = a / d`, in
which the ceiling is an exact natural-number division, so every value is checked by exact
integer arithmetic. The two theorems together give the table of schedule positions, one index
each; the lists have length `r_*(o) + 1 = 11` and `r_*(b) + 1 = 4`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- One step of the schedule recurrence at the original index from a known position and a known
size factor. -/
private lemma schedule_o_succ_of_eq {i p k : ℕ} (hp : schedule .o i = p) (hk : Kstar .o i = k) :
    schedule .o (i + 1) = p + (113 * k * (p + 1) + 999) / 1000 + 10293 := by
  rw [schedule_o_succ_eq_div, hp, hk]

/-- One step of the schedule recurrence at the bootstrap index from a known position and a known
size factor. -/
private lemma schedule_b_succ_of_eq {i p k : ℕ} (hp : schedule .b i = p) (hk : Kstar .b i = k) :
    schedule .b (i + 1) = p + (3 * k * (p + 1) + 24) / 25 + 669 := by
  rw [schedule_b_succ_eq_div, hp, hk]

/-- The eleven schedule positions `p_0(o), …, p_10(o)` at the original index. -/
@[collatz_pos_dens "lem_s02_schedule_values"]
theorem schedule_values_o :
    List.ofFn (fun i : Fin (rStar .o + 1) => schedule .o i) =
      [193, 112161, 20680179, 2948776479, 326497388488, 28144727892821, 1895012673761891,
        99969498591645143, 4155432147958923993, 141268071302011590393,
        17140454471732661035095372255] := by
  have h0 : schedule .o 0 = 193 := rfl
  have h1 := schedule_o_succ_of_eq h0 Kstar_o_zero
  norm_num at h1
  have h2 := schedule_o_succ_of_eq h1 Kstar_o_one
  norm_num at h2
  have h3 := schedule_o_succ_of_eq h2 Kstar_o_two
  norm_num at h3
  have h4 := schedule_o_succ_of_eq h3 Kstar_o_three
  norm_num at h4
  have h5 := schedule_o_succ_of_eq h4 Kstar_o_four
  norm_num at h5
  have h6 := schedule_o_succ_of_eq h5 Kstar_o_five
  norm_num at h6
  have h7 := schedule_o_succ_of_eq h6 Kstar_o_six
  norm_num at h7
  have h8 := schedule_o_succ_of_eq h7 Kstar_o_seven
  norm_num at h8
  have h9 := schedule_o_succ_of_eq h8 Kstar_o_eight
  norm_num at h9
  have h10 := schedule_o_succ_of_eq h9 (Kstar_o_of_nine_le le_rfl)
  norm_num at h10
  simp only [rStar_o, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- The four schedule positions `p_0(b), …, p_3(b)` at the bootstrap index. -/
@[collatz_pos_dens "lem_s02_schedule_values"]
theorem schedule_values_b :
    List.ofFn (fun i : Fin (rStar .b + 1) => schedule .b i) = [169, 15486, 514217, 63701994] := by
  have h0 : schedule .b 0 = 169 := rfl
  have h1 := schedule_b_succ_of_eq h0 Kstar_b_zero
  norm_num at h1
  have h2 := schedule_b_succ_of_eq h1 Kstar_b_one
  norm_num at h2
  have h3 := schedule_b_succ_of_eq h2 Kstar_b_two
  norm_num at h3
  simp only [rStar_b, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ]
  rw [h0, h1, h2, h3]

end CollatzPosDens
