/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Seed.ConcatWord
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.LiftedTransfer

/-!
# The pulled-back reference density

On `G_{q_*}` the pulled-back reference density is
$$\Psi = \sum_{t \in \mathfrak T_{N_*}} \mathcal{T}_{\hat w(t),\,q_*}\,\rho_{k_{N_*}},$$
the sum, over the selected central tuples `t = (w_0, …, w_{N_*-1})` of the first `N_*`
generations, of the lifted transfer to level `q_*` of the reference density at level
`k_{N_*}` along the concatenated word `ŵ(t) = w_0 ⋯ w_{N_*-1}`.

## Main definitions

* `CollatzPosDens.pullbackDensityOf N q`: the same sum with `N_*` and `q_*` replaced by
  parameters `N` and `q`, a function on `G_q`.
* `CollatzPosDens.pullbackDensity`: the pulled-back reference density `Ψ : G_{q_*} → ℝ`.

## Main results

* `CollatzPosDens.pullbackDensity_length_le`: for `t ∈ 𝔗_N`,
  `|ŵ(t)| + k_N ≤ k_N + ∑_{j<N} h_{b_j}`; in particular every summand of `Ψ` is defined.
* `CollatzPosDens.pullbackDensityOf_apply`, `CollatzPosDens.pullbackDensity_def`:
  the defining sums.
* `CollatzPosDens.pullbackDensity_nonneg`: `Ψ ≥ 0`.

## Implementation notes

The lifted transfer `𝒯_{w,q} g` of `g : G_k → ℝ` is only defined when `|w| + k ≤ q`. In the
parametric `pullbackDensityOf` a summand for which this fails is `0`. For the sum defining `Ψ`
it never fails, since `|ŵ(t)| ≤ ∑_{j<N_*} h_{b_j} = q_* - k_{N_*}` for every `t ∈ 𝔗_{N_*}`
(`pullbackDensity_length_le`), so `Ψ` is exactly the sum displayed above.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.6.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For a selected central tuple `t ∈ 𝔗_N`, `|ŵ(t)| + k_N ≤ k_N + ∑_{j<N} h_{b_j}`. -/
theorem pullbackDensity_length_le {N : ℕ} {t : Fin N → Word} (ht : t ∈ selectedTuples N) :
    (concatWord t).length + level N ≤ conductorAt N := by
  rw [conductorAt_def, length_concatWord, add_comm, ← Fin.sum_univ_eq_sum_range]
  exact Nat.add_le_add_left (sum_le_sum fun j _ => length_le_hb_of_mem_firstCrossing
    (centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily ht j))) _

/-- The sum `∑_{t ∈ 𝔗_N} 𝒯_{ŵ(t), q} ρ_{k_N}` on `G_q`, where a summand with
`|ŵ(t)| + k_N > q` (for which the lifted transfer is undefined) is `0`. The pulled-back
reference density is its value at `N = N_*`, `q = q_*`. -/
noncomputable def pullbackDensityOf (N q : ℕ) (y : ResidueGroup q) : ℝ :=
  ∑ t ∈ (selectedTuples_finite N).toFinset,
    if h : (concatWord t).length + level N ≤ q then
      liftedTransfer (concatWord t) h (refDensity (level N)) y
    else 0

/-- The defining sum of `pullbackDensityOf`. -/
theorem pullbackDensityOf_apply (N q : ℕ) (y : ResidueGroup q) :
    pullbackDensityOf N q y = ∑ t ∈ (selectedTuples_finite N).toFinset,
      if h : (concatWord t).length + level N ≤ q then
        liftedTransfer (concatWord t) h (refDensity (level N)) y
      else 0 :=
  rfl

/-- **The pulled-back reference density**
`Ψ = ∑_{t ∈ 𝔗_{N_*}} 𝒯_{ŵ(t), q_*} ρ_{k_{N_*}}` on `G_{q_*}`. -/
@[collatz_pos_dens "def_pullback"]
noncomputable def pullbackDensity : ResidueGroup conductor → ℝ :=
  pullbackDensityOf generationThreshold conductor

/-- `Ψ` is `pullbackDensityOf` at `N = N_*` and `q = q_*`. -/
theorem pullbackDensity_eq_pullbackDensityOf :
    pullbackDensity = pullbackDensityOf generationThreshold conductor :=
  rfl

/-- Every summand of `Ψ` is defined: `|ŵ(t)| + k_{N_*} ≤ q_*` for `t ∈ 𝔗_{N_*}`. -/
theorem pullbackDensity_length_le_conductor {t : Fin generationThreshold → Word}
    (ht : t ∈ selectedTuples generationThreshold) :
    (concatWord t).length + level generationThreshold ≤ conductor :=
  pullbackDensity_length_le ht

/-- The defining sum of `Ψ`, with every summand defined:
`Ψ(y) = ∑_{t ∈ 𝔗_{N_*}} (𝒯_{ŵ(t), q_*} ρ_{k_{N_*}})(y)`. -/
theorem pullbackDensity_def (y : ResidueGroup conductor) :
    pullbackDensity y =
      ∑ t ∈ (selectedTuples_finite generationThreshold).toFinset.attach,
      liftedTransfer (concatWord t.1)
        (pullbackDensity_length_le_conductor
          ((selectedTuples_finite _).mem_toFinset.1 t.2))
        (refDensity (level generationThreshold)) y := by
  rw [pullbackDensity_eq_pullbackDensityOf, pullbackDensityOf_apply, ← sum_attach]
  refine sum_congr rfl fun t _ => ?_
  rw [dite_eq_left]

/-- `pullbackDensityOf` is nonnegative. -/
theorem pullbackDensityOf_nonneg (N q : ℕ) (y : ResidueGroup q) :
    0 ≤ pullbackDensityOf N q y := by
  rw [pullbackDensityOf_apply]
  refine sum_nonneg fun t _ => ?_
  split_ifs with h
  · exact liftedTransfer_nonneg _ h (fun z => refDensity_nonneg _ z) y
  · exact le_rfl

/-- The pulled-back reference density is nonnegative. -/
theorem pullbackDensity_nonneg (y : ResidueGroup conductor) : 0 ≤ pullbackDensity y :=
  pullbackDensityOf_nonneg _ _ y

end CollatzPosDens
