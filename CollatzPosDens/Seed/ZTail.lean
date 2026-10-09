/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Recipe.Varrho
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.NstarTail
public import CollatzPosDens.Seed.CentralIncrement
public import CollatzPosDens.Recipe.MomentTail

/-!
# Uniform variation of `Z_n` beyond the generation threshold

Let `M` be an odd positive integer and `n ≥ N_*`. Then
$$|Z_n(M) - Z_{N_*}(M)| < \frac{47}{32} 2^{-24}.$$

Since `N_* = 9766262 ≥ 9200000`, the central increment bound applies at every `j ≥ N_*`, so by
the triangle inequality
`|Z_n(M) - Z_{N_*}(M)| ≤ ∑_{j=N_*}^{n-1} F j^{5/2} ϱ^j ≤ F ∑_{j ≥ N_*} j^{5/2} ϱ^j`,
a convergent series of nonnegative terms, which is less than `(47/32) 2^{-24}` by the central
tail bound beyond `N_*`.

## Main results

* `CollatzPosDens.abs_weightedCentralSum_sub_generationThreshold_lt`: the bound above.

## Implementation notes

The integer `M` is cast to `ℚ`, as in the definition of `Z_n(M)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- For an odd positive integer `M` and `n ≥ N_*`, `|Z_n(M) - Z_{N_*}(M)| < (47/32) 2^{-24}`. -/
@[collatz_pos_dens "lem_Z_tail"]
theorem abs_weightedCentralSum_sub_generationThreshold_lt {M : ℤ} (hodd : Odd M) (hM : 0 < M)
    {n : ℕ} (hn : generationThreshold ≤ n) :
    |weightedCentralSum n M - weightedCentralSum generationThreshold M| <
      47 / 32 * (2 : ℝ) ^ (-24 : ℤ) := by
  set N := generationThreshold with hNdef
  have hN : 9200000 ≤ N := by rw [hNdef, generationThreshold_eq]; norm_num
  set g : ℕ → ℝ := fun j => (j : ℝ) ^ (5 / 2 : ℝ) * errorDecayRatio ^ j
  obtain ⟨hs, htail⟩ := generationThreshold_central_tail_lt
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    have := errorDecayRatio_nonneg
    positivity
  have hF0 : 0 ≤ errorPrefactor := errorPrefactor_pos.le
  have h1 : |weightedCentralSum n M - weightedCentralSum N M| ≤
      ∑ j ∈ Ico N n, errorPrefactor * g j := by
    rw [abs_sub_comm, ← Real.dist_eq]
    refine (dist_le_Ico_sum_dist (fun j => weightedCentralSum j M) hn).trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Real.dist_eq, abs_sub_comm]
    have := abs_weightedCentralSum_succ_sub_le hodd hM (hN.trans (mem_Ico.1 hj).1)
    simpa only [g, mul_assoc] using this
  have h2 : ∑ j ∈ Ico N n, g j ≤ ∑' j : Set.Ici N, g j := by
    have := hs.sum_le_tsum ((Ico N n).subtype (· ∈ Set.Ici N)) (fun j _ => hg0 j)
    rwa [Finset.sum_subtype_of_mem g (p := (· ∈ Set.Ici N))
      (fun j hj => Set.mem_Ici.2 (mem_Ico.1 hj).1)] at this
  rw [← Finset.mul_sum] at h1
  exact h1.trans_lt ((mul_le_mul_of_nonneg_left h2 hF0).trans_lt htail)

end CollatzPosDens
