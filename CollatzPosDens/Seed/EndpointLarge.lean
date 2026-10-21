/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Seed.S05EndpointGrowthEb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Seed.S05HistoryStep
public import CollatzPosDens.Maps.InverseOrbitOdd

/-!
# Growth of the endpoints of a central history

Let `t` be an odd integer with `t ≥ t_min`, where `t_min = 16^{b_0}` is the target floor, let
`n ≥ 0` and `h ∈ 𝓗_n(t)`. Then for every `0 ≤ j ≤ n` the generation-`j` endpoint `R_j(h)` is an
odd integer with `R_j(h) ≥ 16^{b_j}`.

The base case is `R_0(h) = t ≥ t_min = 16^{b_0}`. For `0 ≤ j < n` the endpoint `R_j(h)` is a
positive odd integer from which `w_j` is admissible, and `R_{j+1}(h) = src(w_j, R_j(h))` is
again a positive odd integer. Every scale satisfies `b_j ≥ b_0 = 16544 ≥ 256`, so induction on
`j`, with the step `R_{j+1}(h) > 16^{e_{b_j}} R_j(h) ≥ 16^{b_j + e_{b_j}} = 16^{b_{j+1}}`, gives
the bound.

## Main results

* `CollatzPosDens.historyEndpointAt_large`: the endpoint bound, for every `j ≤ n`.
* `CollatzPosDens.historyEndpointAt_large_sixteen_pow_le_endpoint`,
  `CollatzPosDens.historyEndpointAt_large_endpoint_pos`: the case `j = n`, read as
  `R_h ≥ 16^{b_n}` in `ℝ` and as `R_h > 0`.
* `CollatzPosDens.targetFloor_le_iff`: `t_min ≤ t` reads `16^{16544} ≤ t`.
* `CollatzPosDens.two_mul_two_pow_le_sixteen_pow`: `2 · 2^b ≤ 16^b` for `b ≥ 1`.

## Implementation notes

The endpoint `R_j(h)` is a rational number; "`R_j(h)` is an odd integer" is stated as the
existence of an odd `m : ℤ` with `R_j(h) = m`. The corollaries for `j = n` take the floor in its
numerical form `16^{16544} ≤ t`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- For `b ≥ 1`, `2 · 2^b ≤ 16^b` in any ordered semiring. -/
theorem two_mul_two_pow_le_sixteen_pow {K : Type*} [CommSemiring K] [PartialOrder K]
    [IsStrictOrderedRing K] {b : ℕ} (hb : 1 ≤ b) : (2 : K) * 2 ^ b ≤ 16 ^ b :=
  calc (2 : K) * 2 ^ b ≤ 8 ^ b * 2 ^ b := by
        gcongr
        exact (by norm_num : (2 : K) ≤ 8).trans (le_self_pow₀ (by norm_num) (by omega))
    _ = 16 ^ b := by rw [← mul_pow]; norm_num

/-- The floor `t_min ≤ t` on an integer `t`, in its numerical form `16^{16544} ≤ t`. -/
theorem targetFloor_le_iff {t : ℤ} : (targetFloor : ℤ) ≤ t ↔ 16 ^ 16544 ≤ t := by
  rw [targetFloor_eq, Nat.cast_pow, Nat.cast_ofNat]

/-- **Growth of endpoints.** Let `t` be an odd integer with `t ≥ t_min` and `h ∈ 𝓗_n(t)`. Then
for every `j ≤ n` the generation-`j` endpoint `R_j(h)` is an odd integer with
`R_j(h) ≥ 16^{b_j}`. -/
@[collatz_pos_dens "lem_endpoint_large"]
theorem historyEndpointAt_large {t : ℤ} (hodd : Odd t) (ht : (targetFloor : ℤ) ≤ t)
    {h : Fin n → Word} (hh : h ∈ centralHistories t n) {j : ℕ} (hj : j ≤ n) :
    ∃ m : ℤ, historyEndpointAt t h j = m ∧ Odd m ∧ 16 ^ scale j ≤ m := by
  have ht' : (16 : ℤ) ^ scale 0 ≤ t := by
    rw [scale_zero]; exact targetFloor_le_iff.1 ht
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht'
  induction j with
  | zero => exact ⟨t, historyEndpointAt_zero _ _, hodd, ht'⟩
  | succ j ih =>
    have hjn : j < n := hj
    obtain ⟨m, hm, hmodd, hmge⟩ := ih hjn.le
    have hwadm : Admissible (m : ℚ) (h ⟨j, hjn⟩) := by
      rw [← hm]; exact (centralHistories.historyEndpointAt_step htpos hodd hh hjn).2
    have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hmge
    obtain ⟨m', hm', -, hm'odd⟩ := hwadm.exists_src_eq_pos_odd hmpos hmodd
    have hw : h ⟨j, hjn⟩ ∈ centralFamily (scale j) (cap j) :=
      selectedTuples_mem_centralFamily hh.1 ⟨j, hjn⟩
    have hgrow := (sixteen_pow_eb_mul_lt_src_of_mem_centralFamily
      (le_trans (by norm_num) (sixteen544_le_scale j)) hmge hw).le
    refine ⟨m', ?_, hm'odd, ?_⟩
    · rw [historyEndpointAt_succ _ h hjn, hm, hm']
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

/-- The endpoint of a central history from an odd `t ≥ 16^{16544}` satisfies
`R_h ≥ 16^{b_n}`. -/
theorem historyEndpointAt_large_sixteen_pow_le_endpoint {t : ℤ} (hodd : Odd t)
    (ht : 16 ^ 16544 ≤ t) {h : Fin n → Word} (hh : h ∈ centralHistories t n) :
    (16 : ℝ) ^ scale n ≤ (historyEndpoint t h : ℝ) := by
  obtain ⟨m, hm, -, hle⟩ := historyEndpointAt_large hodd (targetFloor_le_iff.2 ht) hh le_rfl
  rw [historyEndpoint, hm, Rat.cast_intCast]
  exact_mod_cast hle

/-- The endpoint of a central history from an odd `t ≥ 16^{16544}` is positive. -/
theorem historyEndpointAt_large_endpoint_pos {t : ℤ} (hodd : Odd t) (ht : 16 ^ 16544 ≤ t)
    {h : Fin n → Word} (hh : h ∈ centralHistories t n) :
    (0 : ℚ) < historyEndpoint t h := by
  obtain ⟨m, hm, -, hmge⟩ := historyEndpointAt_large hodd (targetFloor_le_iff.2 ht) hh le_rfl
  rw [historyEndpoint, hm]
  exact_mod_cast lt_of_lt_of_le (by positivity) hmge

end CollatzPosDens
