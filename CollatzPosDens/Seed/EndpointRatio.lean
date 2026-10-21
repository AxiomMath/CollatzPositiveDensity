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
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.EndpointLowerGrowth
public import CollatzPosDens.Seed.EndpointUpperGrowth

/-!
# Spread of a generation

Let `t` be an odd integer with `t ≥ targetFloor`, `n ≥ 0` and `h, h' ∈ 𝓗_n(t)`.
Then `R_{h'} ≤ 2^{∑_{j<n} (K_j + 3)} R_h`.

Both generation-`0` endpoints equal `t > 0`. For every `0 ≤ j < n` the word `w_j` lies in
`𝒞(b_j, K_j) ⊆ 𝒲(b_j, r_{b_j}, K_j)` and `R_j ≥ 16^{b_j}`, so the endpoints satisfy
`¼ (4/3)^{b_j} R_j(h) ≤ R_{j+1}(h)` and `R_{j+1}(h') ≤ 2^{K_j+1} (4/3)^{b_j} R_j(h')`. Since
`2^{K_j+1} = 2^{K_j+3} · ¼`, induction on `j` gives `R_j(h') ≤ 2^{∑_{i<j} (K_i + 3)} R_j(h)` for
every `j ≤ n`.

## Main results

* `CollatzPosDens.historyEndpoint_le_two_pow_mul`: `R_{h'} ≤ 2^{∑_{j<n} (K_j + 3)} R_h`.
* `CollatzPosDens.historyEndpointAt_le_two_pow_mul`: the same bound at every generation
  `j ≤ n`.

## Implementation notes

A direct argument multiplies the lower and upper growth bounds over `0 ≤ j < n` and divides;
here the ratio bound itself is carried through an induction on `j`, which avoids dividing. The
starting point `t` is an integer, cast to `ℚ` where the histories are taken.

## References

* [Mazur, *Collatz positive density*], §16.2.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- The ratio bound `R_j(h') ≤ 2^{∑_{i<j} (K_i + 3)} R_j(h)` at every generation `j ≤ n`. -/
theorem historyEndpointAt_le_two_pow_mul {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) {h h' : Fin n → Word} (hh : h ∈ centralHistories t n)
    (hh' : h' ∈ centralHistories t n) {j : ℕ} (hj : j ≤ n) :
    historyEndpointAt t h' j ≤
      2 ^ (∑ i ∈ Finset.range j, (cap i + 3)) * historyEndpointAt t h j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j < n := hj
    have ih := ih hjn.le
    obtain ⟨m, hm, -, hmge⟩ := historyEndpointAt_large hodd ht hh hjn.le
    obtain ⟨m', hm', -, hm'ge⟩ := historyEndpointAt_large hodd ht hh' hjn.le
    set b := scale j
    set K := cap j
    set S := ∑ i ∈ Finset.range j, (cap i + 3)
    have hb : 1 ≤ b := le_trans (by norm_num) (sixteen544_le_scale j)
    have hR : (2 : ℚ) * 2 ^ b ≤ historyEndpointAt t h j := by
      rw [hm]
      exact (two_mul_two_pow_le_sixteen_pow hb).trans (by exact_mod_cast hmge)
    have hR' : (0 : ℚ) ≤ historyEndpointAt t h' j := by
      rw [hm']
      exact_mod_cast (by positivity : (0 : ℤ) ≤ _).trans hm'ge
    have hmem : ∀ {g : Fin n → Word}, g ∈ centralHistories t n →
        g ⟨j, hjn⟩ ∈ firstCrossing b (rb b) K := fun hg' =>
      centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily hg'.1 ⟨j, hjn⟩)
    have hw := hmem hh
    have hw' := hmem hh'
    rw [historyEndpointAt_succ t h hjn, historyEndpointAt_succ t h' hjn,
      Finset.sum_range_succ, pow_add]
    calc src (h' ⟨j, hjn⟩) (historyEndpointAt t h' j)
        ≤ 2 ^ (K + 1) * (4 / 3) ^ b * historyEndpointAt t h' j :=
          src_le_of_mem_firstCrossing_rb hw' hR'
      _ ≤ 2 ^ (K + 1) * (4 / 3) ^ b * (2 ^ S * historyEndpointAt t h j) := by gcongr
      _ = 2 ^ S * 2 ^ (K + 3) * (1 / 4 * (4 / 3) ^ b * historyEndpointAt t h j) := by
          rw [pow_add, pow_add]
          ring
      _ ≤ 2 ^ S * 2 ^ (K + 3) * src (h ⟨j, hjn⟩) (historyEndpointAt t h j) := by
          gcongr
          exact endpoint_lower_growth_of_two_mul_two_pow_le hw hR

/-- **Spread of a generation.** Let `t` be an odd integer with `t ≥ targetFloor`, `n ≥ 0`
and `h, h' ∈ 𝓗_n(t)`. Then `R_{h'} ≤ 2^{∑_{j<n} (K_j + 3)} R_h`. -/
@[collatz_pos_dens "lem_endpoint_ratio"]
theorem historyEndpoint_le_two_pow_mul {t : ℤ} (hodd : Odd t) (ht : (targetFloor : ℤ) ≤ t)
    {h h' : Fin n → Word} (hh : h ∈ centralHistories t n)
    (hh' : h' ∈ centralHistories t n) :
    historyEndpoint t h' ≤ 2 ^ (∑ j ∈ Finset.range n, (cap j + 3)) * historyEndpoint t h :=
  historyEndpointAt_le_two_pow_mul hodd ht hh hh' le_rfl

end CollatzPosDens
