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
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Seed.S05TupleLength
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Transfer.FiberSource
public import CollatzPosDens.Transfer.S02LiftedTransfer
public import CollatzPosDens.Transfer.S02Reduction

/-!
# Evaluating the pulled-back reference density at an integer

For every odd positive integer `t`, the weighted central sum of generation `N_*` is the value of
the pulled-back reference density at the residue of `t`: `Z_{N_*}(t) = Ψ(t mod 3^{q_*})`.

For a selected central tuple `τ ∈ 𝔗_{N_*}` with concatenation `w = ŵ(τ)`, the bound
`|w| + k_{N_*} ≤ q_*` of `length_concatWord_add_level_le_conductor` holds, so every tuple
contributes to `Ψ`. By the fiber description of the transfer at an integer point
(`liftedTransfer_intCast`), the lifted transfer of `ρ_{k_{N_*}}` along `w` at `[t]_{q_*}` is
`ω(w) ρ_{k_{N_*}}(src(w, t) mod 3^{k_{N_*}})` when `w` is admissible from `t`, and `0`
otherwise. The tuples with `w` admissible from `t` are exactly the central histories
`h ∈ 𝓗_{N_*}(t)`, with `src(w, t) = R_h`; summing over `τ` gives `Z_{N_*}(t)`.

## Main results

* `CollatzPosDens.weightedCentralSum_eq_pullbackDensityOf`:
  `Z_N(t) = (pullbackDensityOf N q)([t]_q)` whenever `|ŵ(τ)| + k_N ≤ q` for every `τ ∈ 𝔗_N`.
* `CollatzPosDens.weightedCentralSum_eq_pullbackDensity`: `Z_{N_*}(t) = Ψ([t]_{q_*})`.

## Implementation notes

The source takes `t` odd and positive; the identity holds for every integer `t`, and is
stated so. It is proved for the parametric `pullbackDensityOf N q` under the hypothesis that
`|ŵ(τ)| + k_N ≤ q` for every `τ ∈ 𝔗_N`, which at `N = N_*`, `q = q_*` is
`length_concatWord_add_level_le_conductor`.

## References

* [Mazur, *Collatz positive density*], §16.7.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The weighted central sum `Z_N(t)` at an integer `t` is the value of `pullbackDensityOf N q`
at `[t]_q`, whenever `|ŵ(τ)| + k_N ≤ q` for every selected tuple `τ ∈ 𝔗_N`. -/
theorem weightedCentralSum_eq_pullbackDensityOf {N q : ℕ}
    (hq : ∀ τ ∈ selectedTuples N, (concatWord τ).length + level N ≤ q) (t : ℤ) :
    weightedCentralSum N t = pullbackDensityOf N q (t : ResidueGroup q) := by
  rw [weightedCentralSum_eq_sum, pullbackDensityOf_apply]
  have hterm : ∀ τ ∈ (selectedTuples_finite N).toFinset,
      (if h : (concatWord τ).length + level N ≤ q then
        liftedTransfer (concatWord τ) h (refDensity (level N)) (t : ResidueGroup q)
      else 0) =
      if Admissible (t : ℚ) (concatWord τ) then
        ((concatWord τ).weight : ℝ) *
          refDensity (level N) ((historyEndpoint (t : ℚ) τ).num : ResidueGroup (level N))
      else 0 := by
    intro τ hτ
    rw [Set.Finite.mem_toFinset] at hτ
    rw [dite_eq_left (hq τ hτ), liftedTransfer_intCast, historyEndpoint_eq_src]
  rw [sum_congr rfl hterm, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext τ
  simp only [mem_filter, Set.Finite.mem_toFinset, mem_centralHistories]

/-- **Evaluation of the pulled-back density.** For every integer `t` (in particular every odd
positive integer), `Z_{N_*}(t) = Ψ(t mod 3^{q_*})`. -/
@[collatz_pos_dens "lem_pullback_eval"]
theorem weightedCentralSum_eq_pullbackDensity (t : ℤ) :
    weightedCentralSum generationThreshold t = pullbackDensity (t : ResidueGroup conductor) :=
  weightedCentralSum_eq_pullbackDensityOf
    (fun _ hτ => length_concatWord_add_level_le_conductor hτ) t

end CollatzPosDens
