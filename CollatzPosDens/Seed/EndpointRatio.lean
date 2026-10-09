/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.EndpointLowerGrowth
public import CollatzPosDens.Seed.EndpointUpperGrowth

/-!
# Spread of a generation

Let `M` be an odd integer with `16 ^ scale 0 ≤ M`, and let `h, h'` be two histories in
`centralHistories M n`. Then the endpoints satisfy
`historyEndpoint M h' ≤ 2 ^ (∑ j < n, (cap j + 3)) * historyEndpoint M h`.

Write `R_j(h) = historyEndpointAt M h j`, `b_j = scale j` and `K_j = cap j`. For every `j < n`
the word `h j` lies in `firstCrossing b_j (rb b_j) K_j` and `R_j(h) ≥ 16 ^ b_j`, so
`¼ (4/3)^{b_j} R_j(h) ≤ R_{j+1}(h)` and `R_{j+1}(h') ≤ 2^{K_j+1} (4/3)^{b_j} R_j(h')`. Since
`2^{K_j+1} = 2^{K_j+3} · ¼`, induction on `j` gives `R_j(h') ≤ 2^{∑_{i<j} (K_i + 3)} R_j(h)` for
every `j ≤ n`.

## Main results

* `CollatzPosDens.historyEndpoint_le_two_pow_mul`: the bound on the ratio of the endpoints of two
  central histories of length `n`.
* `CollatzPosDens.historyEndpointAt_le_two_pow_mul`: the same bound at every generation `j ≤ n`.

## Implementation notes

The ratio bound itself is carried through the induction, rather than multiplying the lower and
upper growth bounds over `j < n` and dividing. The starting point `M` is an integer, cast to `ℚ`
where the histories are taken.

## References

* [Mazur, *Collatz positive density*], §17.2.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- The ratio bound `R_j(h') ≤ 2^{∑_{i<j} (K_i + 3)} R_j(h)` at every generation `j ≤ n`. -/
theorem historyEndpointAt_le_two_pow_mul {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) {h h' : Fin n → Word} (hh : h ∈ centralHistories M n)
    (hh' : h' ∈ centralHistories M n) {j : ℕ} (hj : j ≤ n) :
    historyEndpointAt M h' j ≤
      2 ^ (∑ i ∈ Finset.range j, (cap i + 3)) * historyEndpointAt M h j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j < n := hj
    have ih := ih hjn.le
    obtain ⟨m, hm, -, hmge⟩ := historyEndpointAt_large hodd hM hh hjn.le
    obtain ⟨m', hm', -, hm'ge⟩ := historyEndpointAt_large hodd hM hh' hjn.le
    set b := scale j
    set K := cap j
    set S := ∑ i ∈ Finset.range j, (cap i + 3)
    have hb : 1 ≤ b := le_trans (by norm_num) (nine_le_scale j)
    have hR : (2 : ℚ) * 2 ^ b ≤ historyEndpointAt M h j := by
      rw [hm]
      exact (two_mul_two_pow_le_sixteen_pow hb).trans (by exact_mod_cast hmge)
    have hR' : (0 : ℚ) ≤ historyEndpointAt M h' j := by
      rw [hm']
      exact_mod_cast (by positivity : (0 : ℤ) ≤ _).trans hm'ge
    have hw : h ⟨j, hjn⟩ ∈ firstCrossing b (rb b) K :=
      centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily hh.1 ⟨j, hjn⟩)
    have hw' : h' ⟨j, hjn⟩ ∈ firstCrossing b (rb b) K :=
      centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily hh'.1 ⟨j, hjn⟩)
    rw [historyEndpointAt_succ M h hjn, historyEndpointAt_succ M h' hjn,
      Finset.sum_range_succ, pow_add]
    calc src (h' ⟨j, hjn⟩) (historyEndpointAt M h' j)
        ≤ 2 ^ (K + 1) * (4 / 3) ^ b * historyEndpointAt M h' j :=
          src_le_of_mem_firstCrossing_rb hw' hR'
      _ ≤ 2 ^ (K + 1) * (4 / 3) ^ b * (2 ^ S * historyEndpointAt M h j) := by gcongr
      _ = 2 ^ S * 2 ^ (K + 3) * (1 / 4 * (4 / 3) ^ b * historyEndpointAt M h j) := by
          rw [pow_add, pow_add]
          ring
      _ ≤ 2 ^ S * 2 ^ (K + 3) * src (h ⟨j, hjn⟩) (historyEndpointAt M h j) := by
          gcongr
          exact endpoint_lower_growth_of_two_mul_two_pow_le hw hR

/-- **Spread of a generation.** If `M` is an odd integer with `16 ^ scale 0 ≤ M` and `h, h'` lie
in `centralHistories M n`, then
`historyEndpoint M h' ≤ 2 ^ (∑ j < n, (cap j + 3)) * historyEndpoint M h`. -/
@[collatz_pos_dens "lem_endpoint_ratio"]
theorem historyEndpoint_le_two_pow_mul {M : ℤ} (hodd : Odd M) (hM : 16 ^ scale 0 ≤ M)
    {h h' : Fin n → Word} (hh : h ∈ centralHistories M n) (hh' : h' ∈ centralHistories M n) :
    historyEndpoint M h' ≤ 2 ^ (∑ j ∈ Finset.range n, (cap j + 3)) * historyEndpoint M h :=
  historyEndpointAt_le_two_pow_mul hodd hM hh hh' le_rfl

end CollatzPosDens
