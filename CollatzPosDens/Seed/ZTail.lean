/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhEj
public import CollatzPosDens.Recipe.TailMargin
public import CollatzPosDens.Recipe.ZMargin
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Recipe.NstarTail
public import CollatzPosDens.Seed.CentralIncrement

/-!
# Tail of the variation of `Z_n` beyond the generation threshold

Let `t` be an odd positive integer and `n ≥ N_*`. The central increment bound
`|Z_{j+1}(t) - Z_j(t)| ≤ E_j` applies at every `j` with `N_* ≤ j < n`, so by the triangle
inequality and the tail bound for the propagation majorant beyond `N_*`,
$$|Z_n(t) - Z_{N_*}(t)| \le \sum_{j=N_*}^{n-1} |Z_{j+1}(t) - Z_j(t)|
  \le \sum_{j=N_*}^{n-1} E_j < θ_{tl}$$
(for `n = N_*` both sums are empty). Hence `Z_{N_*}(t) > θ_{tl} + ε_Z` forces `Z_n(t) > ε_Z`,
where `θ_{tl} = tailMargin` (`= 6/7`) and `ε_Z = centralSumMargin` (`= 2^{-28}`).

## Main results

* `CollatzPosDens.abs_weightedCentralSum_sub_weightedCentralSum_generationThreshold_lt`: the
  variation bound `|Z_n(t) - Z_{N_*}(t)| < θ_{tl}`.
* `CollatzPosDens.abs_weightedCentralSum_sub_generationThreshold_lt`: if
  `Z_{N_*}(t) > θ_{tl} + ε_Z` then `Z_n(t) > ε_Z`.

## Implementation notes

The integer `t` is cast to `ℚ`, as in the definition of `Z_n(t)`.

## References

* [Mazur, *Collatz positive density*], §16.5.
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- **Variation of `Z_n` beyond `N_*`.** For an odd positive integer `t` and `n ≥ N_*`,
`|Z_n(t) - Z_{N_*}(t)| < θ_{tl}`. -/
theorem abs_weightedCentralSum_sub_weightedCentralSum_generationThreshold_lt {t : ℤ}
    (hodd : Odd t) (ht : 0 < t) {n : ℕ} (hn : generationThreshold ≤ n) :
    |weightedCentralSum n t - weightedCentralSum generationThreshold t| <
      (tailMargin : ℝ) := by
  rw [abs_sub_comm, ← Real.dist_eq]
  refine (dist_le_Ico_sum_dist (fun j => weightedCentralSum j t) hn).trans_lt ?_
  refine lt_of_le_of_lt (Finset.sum_le_sum fun j hj => ?_)
    (sum_Ico_generationThreshold_propagationMajorant_lt n)
  rw [Real.dist_eq, abs_sub_comm]
  exact abs_weightedCentralSum_succ_sub_le hodd ht (mem_Ico.1 hj).1

/-- **Tail of the variation.** For an odd positive integer `t` with
`Z_{N_*}(t) > θ_{tl} + ε_Z` and `n ≥ N_*`, `Z_n(t) > ε_Z`. -/
@[collatz_pos_dens "lem_Z_tail"]
theorem abs_weightedCentralSum_sub_generationThreshold_lt {t : ℤ} (hodd : Odd t) (ht : 0 < t)
    (hZ : (tailMargin : ℝ) + centralSumMargin < weightedCentralSum generationThreshold t)
    {n : ℕ} (hn : generationThreshold ≤ n) :
    (centralSumMargin : ℝ) < weightedCentralSum n t := by
  have h := (abs_sub_lt_iff.1
    (abs_weightedCentralSum_sub_weightedCentralSum_generationThreshold_lt hodd ht hn)).2
  linarith

end CollatzPosDens
