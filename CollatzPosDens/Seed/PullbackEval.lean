/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Pullback
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Transfer.FiberSource
public import CollatzPosDens.Transfer.LiftedTransfer
public import CollatzPosDens.Transfer.Reduction

/-!
# Evaluating the pulled-back reference density at an integer

For every odd positive integer `M`, the weighted central sum of generation `N_*` is the value of
the pulled-back reference density at the residue of `M`: `Z_{N_*}(M) = Ψ(M mod 3^{q_*})`.

For a selected central tuple `t ∈ 𝔗_{N_*}` with concatenation `w = ŵ(t)`, the words of `t`
have lengths at most `h_{b_i}`, so `|w| + k_{N_*} ≤ q_*`. By the fiber description of the
transfer at an integer point, the lifted transfer of `ρ_{k_{N_*}}` along `w` at `[M]_{q_*}` is
`ω(w) ρ_{k_{N_*}}(src(w, M) mod 3^{k_{N_*}})` when `w` is admissible from `M`, and `0`
otherwise. The tuples with `w` admissible from `M` are exactly the central histories
`h ∈ 𝓗_{N_*}(M)`, with `src(w, M) = R_h`; summing over `t` gives `Z_{N_*}(M)`.

## Main results

* `CollatzPosDens.weightedCentralSum_eq_pullbackDensityOf`:
  `Z_N(M) = (pullbackDensityOf N q)([M]_q)` whenever `k_N + ∑_{i<N} h_{b_i} ≤ q`.
* `CollatzPosDens.weightedCentralSum_eq_pullbackDensity`: `Z_{N_*}(M) = Ψ([M]_{q_*})`.

## Implementation notes

The source takes `M` odd and positive; the identity holds for every integer `M`, and is stated
so. It is proved for the parametric `pullbackDensityOf N q` under the hypothesis
`k_N + ∑_{i<N} h_{b_i} ≤ q`, which at `N = N_*`, `q = q_*` is the definition of `q_*`.

## References

* [Mazur, *Collatz positive density*], §17.6.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The weighted central sum `Z_N(M)` at an integer `M` is the value of `pullbackDensityOf N q`
at `[M]_q`, whenever `k_N + ∑_{i<N} h_{b_i} ≤ q`. -/
theorem weightedCentralSum_eq_pullbackDensityOf {N q : ℕ} (hq : conductorAt N ≤ q) (M : ℤ) :
    weightedCentralSum N M = pullbackDensityOf N q (M : ResidueGroup q) := by
  rw [weightedCentralSum_eq_sum, pullbackDensityOf_apply]
  have hterm : ∀ t ∈ (selectedTuples_finite N).toFinset,
      (if h : (concatWord t).length + level N ≤ q then
        liftedTransfer (concatWord t) h (refDensity (level N)) (M : ResidueGroup q)
      else 0) =
      if Admissible (M : ℚ) (concatWord t) then
        ((concatWord t).weight : ℝ) *
          refDensity (level N) ((historyEndpoint (M : ℚ) t).num : ResidueGroup (level N))
      else 0 := by
    intro t ht
    rw [Set.Finite.mem_toFinset] at ht
    have hlen : (concatWord t).length + level N ≤ q := (pullbackDensity_length_le ht).trans hq
    rw [dite_eq_left hlen, liftedTransfer_intCast, historyEndpoint_eq_src]
  rw [sum_congr rfl hterm, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext t
  simp [mem_centralHistories]

/-- **Evaluation of the pulled-back density.** For every integer `M` (in particular every odd
positive integer), `Z_{N_*}(M) = Ψ(M mod 3^{q_*})`. -/
@[collatz_pos_dens "lem_pullback_eval"]
theorem weightedCentralSum_eq_pullbackDensity (M : ℤ) :
    weightedCentralSum generationThreshold M = pullbackDensity (M : ResidueGroup conductor) :=
  weightedCentralSum_eq_pullbackDensityOf le_rfl M

end CollatzPosDens
