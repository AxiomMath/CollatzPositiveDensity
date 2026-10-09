/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Seed.EndpointGrowthEb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Maps.ConcatAdmissible

/-!
# Growth of the endpoints of a central history

Let `M` be an odd integer with `M ≥ 16^{b₀}`, `n ≥ 0` and `h ∈ 𝓗_n(M)`. Then for every
`0 ≤ j ≤ n` the generation-`j` endpoint `R_j(h)` is an odd integer with `R_j(h) ≥ 16^{b_j}`.

Every prefix `w₀ ⋯ w_{j-1}` of the concatenated word is admissible from `M`, so `w_j` is
admissible from `R_j(h)` and `R_{j+1}(h) = src(w_j, R_j(h))`; in particular each endpoint is a
positive odd integer. Induction on `j`, with the step
`R_{j+1}(h) > 16^{e_{b_j}} R_j(h) ≥ 16^{b_j + e_{b_j}} = 16^{b_{j+1}}`, gives the bound.

## Main results

* `CollatzPosDens.historyEndpointAt_large`: for every `j ≤ n`, `R_j(h)` is an odd integer with
  `R_j(h) ≥ 16^{b_j}`.
* `CollatzPosDens.historyEndpointAt_large_sixteen_pow_le_endpoint`,
  `CollatzPosDens.historyEndpointAt_large_endpoint_pos`: the case `j = n`, read as
  `R_h ≥ 16^{b_n}` in `ℝ` and as `R_h > 0`.
* `CollatzPosDens.two_mul_two_pow_le_sixteen_pow`: `2 · 2^b ≤ 16^b` for `b ≥ 1`.

## Implementation notes

The endpoint `R_j(h)` is a rational number; "`R_j(h)` is an odd integer" is stated as the
existence of an odd `m : ℤ` with `R_j(h) = m`.

## References

* [Mazur, *Collatz positive density*], §17.2.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- For `b ≥ 1`, `2 · 2^b ≤ 16^b` in any strictly ordered commutative semiring. -/
theorem two_mul_two_pow_le_sixteen_pow {K : Type*} [CommSemiring K] [PartialOrder K]
    [IsStrictOrderedRing K] {b : ℕ} (hb : 1 ≤ b) : (2 : K) * 2 ^ b ≤ 16 ^ b :=
  calc (2 : K) * 2 ^ b ≤ 8 ^ b * 2 ^ b := by
        gcongr
        exact (by norm_num : (2 : K) ≤ 8).trans (le_self_pow₀ (by norm_num) (by omega))
    _ = 16 ^ b := by rw [← mul_pow]; norm_num

/-- Every prefix `w₀ ⋯ w_{j-1}` of a history whose concatenated word is admissible from `M` is
admissible from `M`. -/
private theorem admissible_take_flatten {M : ℚ} {h : Fin n → Word}
    (hadm : Admissible M (concatWord h)) (j : ℕ) :
    Admissible M ((List.ofFn h).take j).flatten := by
  rw [concatWord, ← List.take_append_drop j (List.ofFn h), List.flatten_append] at hadm
  exact (admissible_append.1 hadm).1

/-- **Growth of endpoints.** Let `M` be an odd integer with `M ≥ 16^{b₀}` and
`h ∈ 𝓗_n(M)`. Then for every `0 ≤ j ≤ n` the generation-`j` endpoint `R_j(h)` is an odd
integer with `R_j(h) ≥ 16^{b_j}`. -/
@[collatz_pos_dens "lem_endpoint_large"]
theorem historyEndpointAt_large {M : ℤ} (hodd : Odd M) (hM : 16 ^ scale 0 ≤ M)
    {h : Fin n → Word} (hh : h ∈ centralHistories M n) {j : ℕ} (hj : j ≤ n) :
    ∃ m : ℤ, historyEndpointAt M h j = m ∧ Odd m ∧ 16 ^ scale j ≤ m := by
  induction j with
  | zero => exact ⟨M, historyEndpointAt_zero _ _, hodd, hM⟩
  | succ j ih =>
    have hjn : j < n := hj
    obtain ⟨m, hm, hmodd, hmge⟩ := ih hjn.le
    have hpre := admissible_take_flatten hh.2 (j + 1)
    rw [flatten_take_succ_ofFn h hjn, admissible_append] at hpre
    have hwadm : Admissible (m : ℚ) (h ⟨j, hjn⟩) := by
      rw [← hm]; exact hpre.2
    have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hmge
    obtain ⟨m', hm', -, hm'odd⟩ := hwadm.exists_src_eq_pos_odd hmpos hmodd
    have hw : h ⟨j, hjn⟩ ∈ centralFamily (scale j) (cap j) :=
      selectedTuples_mem_centralFamily hh.1 ⟨j, hjn⟩
    have hgrow :=
      (sixteen_pow_eb_mul_lt_src_of_mem_centralFamily (nine_le_scale j) hmge hw).le
    refine ⟨m', ?_, hm'odd, ?_⟩
    · rw [historyEndpointAt_succ M h hjn, hm, hm']
    · rw [hm'] at hgrow
      have hmge' : ((16 : ℤ) ^ scale j : ℚ) ≤ m := by exact_mod_cast hmge
      have key : ((16 : ℤ) ^ scale (j + 1) : ℚ) ≤ m' := by
        rw [scale_succ, pow_add]
        push_cast at hmge' ⊢
        calc (16 : ℚ) ^ scale j * 16 ^ eb (scale j) = 16 ^ eb (scale j) * 16 ^ scale j := by
              ring
          _ ≤ 16 ^ eb (scale j) * m := by gcongr
          _ ≤ m' := hgrow
      exact_mod_cast key

/-- The endpoint of a central history from an odd `M ≥ 16^{b₀}` satisfies `R_h ≥ 16^{b_n}`. -/
theorem historyEndpointAt_large_sixteen_pow_le_endpoint {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) {h : Fin n → Word} (hh : h ∈ centralHistories M n) :
    (16 : ℝ) ^ scale n ≤ (historyEndpoint M h : ℝ) := by
  obtain ⟨m, hm, -, hle⟩ := historyEndpointAt_large hodd hM hh le_rfl
  rw [historyEndpoint, hm, Rat.cast_intCast]
  exact_mod_cast hle

/-- The endpoint of a central history from an odd `M ≥ 16^{b₀}` is positive. -/
theorem historyEndpointAt_large_endpoint_pos {M : ℤ} (hodd : Odd M) (hM : 16 ^ scale 0 ≤ M)
    {h : Fin n → Word} (hh : h ∈ centralHistories M n) : (0 : ℚ) < historyEndpoint M h := by
  obtain ⟨m, hm, -, hmge⟩ := historyEndpointAt_large hodd hM hh le_rfl
  rw [historyEndpoint, hm]
  exact_mod_cast lt_of_lt_of_le (by positivity) hmge

end CollatzPosDens
