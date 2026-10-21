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
public import CollatzPosDens.Seed.S05ConcatWord
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.S02LiftedTransfer

/-!
# The pulled-back reference density

Write `q_*` for `CollatzPosDens.conductor`, `N_*` for `CollatzPosDens.generationThreshold`,
`G_q` for `CollatzPosDens.ResidueGroup q`, `𝔗_N` for `CollatzPosDens.selectedTuples N`, `k_N` for
`CollatzPosDens.level N` and `ρ_k` for `CollatzPosDens.refDensity k`. On `G_{q_*}` the pulled-back
reference density is
$$\Psi = \sum_{\substack{t \in \mathfrak T_{N_*}\\ |\hat w(t)| + k_{N_*} \le q_*}}
  \mathcal{T}_{\hat w(t),\,q_*}\,\rho_{k_{N_*}},$$
the sum, over the selected central tuples `t = (w_0, …, w_{N_*-1})` of generations
`0, …, N_* - 1` whose concatenated word `ŵ(t) = w_0 ⋯ w_{N_*-1}` fits below the
conductor, of the lifted transfer to level `q_*` of the reference density at level `k_{N_*}`
along `ŵ(t)`.

## Main definitions

* `CollatzPosDens.neZero_three_pow_conductor`: the instance `NeZero (3 ^ q_*)` from which the
  finite type `G_{q_*}` is built.
* `CollatzPosDens.pullbackDensityOf`: for `N q : ℕ`, the same sum with `N_*` and `q_*` replaced by
  parameters `N` and `q`, a function on `G_q`.
* `CollatzPosDens.pullbackDensity`: the pulled-back reference density `Ψ : G_{q_*} → ℝ`.

## Main results

* `CollatzPosDens.pullbackDensity_length_le`: for `τ ∈ 𝔗_N`,
  `|ŵ(τ)| + k_N ≤ k_N + ∑_{j<N} h_{b_j}`.
* `CollatzPosDens.pullbackDensityOf_apply`, `CollatzPosDens.pullbackDensity_def`:
  the defining sums.
* `CollatzPosDens.pullbackDensity_nonneg`: `Ψ ≥ 0`.

## Implementation notes

The lifted transfer `𝒯_{w,q} g` of `g : G_k → ℝ` is only defined when `|w| + k ≤ q`. In
`pullbackDensityOf` the sum runs over all of `𝔗_N`, a summand for which this fails being `0`;
this is the sum over the tuples satisfying the condition, which is the form of
`pullbackDensity_def`.

The conductor `q_*` is irreducible, so elaboration never tries to evaluate `3^{q_*}`; nothing
here depends on its value. The kernel does unfold it, and checking that the general instance
`Nat.instNeZeroHPow` has the type `NeZero (3 ^ q_*)` in which `G_{q_*}` is written makes it
evaluate `3^{q_*}`. The instance `neZero_three_pow_conductor` is stated in that exact form, and
the finite type `G_{q_*}` is built from it; results about sums over `G_q` that are to be used at
`q = q_*` take `[NeZero (3 ^ q)]` as an argument for the same reason.

A selected tuple `τ = (w_0, …, w_{N-1})` is a map `Fin N → Word`.

## References

* [Mazur, *Collatz positive density*], §16.7.
-/

@[expose] public section

namespace CollatzPosDens

open Finset


/-- `3^{q_*} ≠ 0`, as an instance stated in the form in which `ResidueGroup conductor` is
written, so that the finite type `G_{q_*}` is never compared with the general instance
`Nat.instNeZeroHPow`, a comparison which unfolds `3^{q_*}`. -/
instance (priority := high) neZero_three_pow_conductor : NeZero (3 ^ conductor) :=
  ⟨pow_ne_zero _ (by norm_num)⟩

/-- For a selected central tuple `τ = (w_0, …, w_{N-1}) ∈ 𝔗_N`,
`|ŵ(τ)| + k_N ≤ k_N + ∑_{j<N} h_{b_j}`. -/
theorem pullbackDensity_length_le {N : ℕ} {t : Fin N → Word}
    (ht : t ∈ selectedTuples N) :
    (concatWord t).length + level N ≤ conductorAt N := by
  rw [conductorAt_def, length_concatWord, add_comm]
  refine Nat.add_le_add_left ?_ _
  calc ∑ k, (t k).length ≤ ∑ k : Fin N, hb (scale (k : ℕ)) :=
        sum_le_sum fun k _ => length_le_hb_of_mem_firstCrossing
          (centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily ht k))
    _ = ∑ j ∈ range N, hb (scale j) := Fin.sum_univ_eq_sum_range (fun k => hb (scale k)) N

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
`Ψ = ∑_{t ∈ 𝔗_{N_*}, |ŵ(t)| + k_{N_*} ≤ q_*} 𝒯_{ŵ(t), q_*} ρ_{k_{N_*}}` on `G_{q_*}`. -/
@[collatz_pos_dens "def_pullback"]
noncomputable def pullbackDensity : ResidueGroup conductor → ℝ :=
  pullbackDensityOf generationThreshold conductor

/-- `Ψ` is `pullbackDensityOf` at `N = N_*` and `q = q_*`. -/
theorem pullbackDensity_eq_pullbackDensityOf :
    pullbackDensity = pullbackDensityOf generationThreshold conductor :=
  rfl

/-- The defining sum of `Ψ` as in its definition, over the selected tuples that fit below the
conductor: `Ψ(y) = ∑_{t ∈ 𝔗_{N_*}, |ŵ(t)| + k_{N_*} ≤ q_*} (𝒯_{ŵ(t), q_*} ρ_{k_{N_*}})(y)`. -/
theorem pullbackDensity_def (y : ResidueGroup conductor) :
    pullbackDensity y =
      ∑ t ∈ ((selectedTuples_finite generationThreshold).toFinset.filter fun t =>
          (concatWord t).length + level generationThreshold ≤ conductor).attach,
      liftedTransfer (concatWord t.1) (mem_filter.1 t.2).2
        (refDensity (level generationThreshold)) y := by
  rw [pullbackDensity_eq_pullbackDensityOf, pullbackDensityOf_apply, sum_dite,
    sum_const_zero, add_zero, univ_eq_attach]

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
