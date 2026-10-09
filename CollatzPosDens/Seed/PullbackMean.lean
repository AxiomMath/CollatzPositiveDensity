/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Seed.Pullback
public import CollatzPosDens.Transfer.RefDensityMean
public import CollatzPosDens.Transfer.TransferAbsMean
public import CollatzPosDens.Transfer.TransferMean

/-!
# The mean of the pulled-back reference density

The pulled-back reference density `Ψ = ∑_{t ∈ 𝔗_{N_*}} 𝒯_{ŵ(t), q_*} ρ_{k_{N_*}}` on
`G_{q_*}` has mean
$$\langle \Psi\rangle_{q_*} = \tfrac23 \sum_{t\in\mathfrak T_{N_*}} 2^{-A(\hat w(t))}.$$
Every selected tuple `t` has `|ŵ(t)| + k_{N_*} ≤ q_*`, so each summand of `Ψ` is a genuine
lifted transfer. For a word `w` with `|w| + k ≤ Q`, the lifted transfer
`𝒯_{w,Q} ρ_k = 𝒯_w (ρ_k ∘ π_{Q-|w|,k})` has mean
`2^{-A(w)} ⟨ρ_k⟩_k = 2/3 · 2^{-A(w)}` (`CollatzPosDens.residueAvg_liftedTransfer` and
`CollatzPosDens.residueAvg_refDensity`), since all fibres of a reduction map have the same
size. Summing over the finite set `𝔗_{N_*}` gives the claim.

## Main results

* `CollatzPosDens.residueAvg_pullbackDensityOf`: the mean identity for
  `pullbackDensityOf N q` whenever `k_N + ∑_{i<N} h_{b_i} ≤ q`.
* `CollatzPosDens.residueAvg_pullbackDensity`:
  `⟨Ψ⟩_{q_*} = 2/3 · ∑_{t ∈ 𝔗_{N_*}} 2^{-A(ŵ(t))}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The mean of `pullbackDensityOf N q`: whenever `k_N + ∑_{i<N} h_{b_i} ≤ q`,
`⟨pullbackDensityOf N q⟩_q = 2/3 · ∑_{t ∈ 𝔗_N} 2^{-A(ŵ(t))}`. -/
theorem residueAvg_pullbackDensityOf {N q : ℕ} (hq : conductorAt N ≤ q) :
    residueAvg q (pullbackDensityOf N q) =
      2 / 3 * ∑ t ∈ (selectedTuples_finite N).toFinset,
        (2 : ℝ) ^ (-((concatWord t).valSum : ℤ)) := by
  rw [residueAvg_def]
  simp_rw [pullbackDensityOf_apply]
  rw [sum_comm, mul_sum, mul_sum]
  refine sum_congr rfl fun t ht => ?_
  have hlen : (concatWord t).length + level N ≤ q :=
    (pullbackDensity_length_le ((selectedTuples_finite N).mem_toFinset.1 ht)).trans
      hq
  simp only [dite_eq_left hlen]
  rw [← residueAvg_def, residueAvg_liftedTransfer, residueAvg_refDensity, mul_comm]

/-- **Mean of the pullback.** `⟨Ψ⟩_{q_*} = 2/3 · ∑_{t ∈ 𝔗_{N_*}} 2^{-A(ŵ(t))}`. -/
@[collatz_pos_dens "lem_pullback_mean"]
theorem residueAvg_pullbackDensity :
    residueAvg conductor pullbackDensity =
      2 / 3 * ∑ t ∈ (selectedTuples_finite generationThreshold).toFinset,
        (2 : ℝ) ^ (-((concatWord t).valSum : ℤ)) :=
  residueAvg_pullbackDensityOf conductor_eq_conductorAt.ge

end CollatzPosDens
