/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrMomentBlack
public import CollatzPosDens.StoppingTrace.TrKernelTwo
public import CollatzPosDens.Transfer.S02Theta

/-!
# The trace mass from a black origin

Let `v` be a black point, `N ∈ ℕ` with `j(v) + N > ⌊n/2⌋`, and `k ∈ ℕ`. Then the `bw^⊗`-weighted
sum of the `(k+1)`-st trace moments over the block lists `β ∈ 𝔅^N` is at most the entry weight
`θ^en_k = (1 - d_entry)^k = (77/100)^k`:
`∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵_{k+1}(v, β) ≤ θ^en_k`.

The left side equals the kernel power `m_k(v)` (`tsum_trListWeight_mul_trMoment_eq_trKernel`),
and `m_k(v) ≤ θ^en_k` (`trKernel_two_le_rhoStar`).

## Main results

* `CollatzPosDens.exp_gammaStar_mul_rhoStar_pow_lt`:
  `∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵_{k+1}(v, β) ≤ θ^en_k`.

## Implementation notes

The sum is taken in `[0, ∞]`, each term being `ofReal (bw^⊗(β)) * ofReal (𝒵_{k+1}(v, β))`, and
is bounded by `ENNReal.ofReal θ^en_k`; in particular the sum is finite. Black points lie in `𝒫`
and the residue `ξ` is a unit; these standing assumptions are the hypotheses `v ∈ bkPoints` and
`IsResidueUnit ξ`.

## References

* [Mazur, *Collatz positive density*], §9.10.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The trace mass from a black origin.** Let `ξ ∈ G_n` be a unit, `v ∈ 𝒫` black
for `(n, ξ, ε_*)`, `N ∈ ℕ` with `j(v) + N > ⌊n/2⌋`, and `k ∈ ℕ`. Then
`∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵_{k+1}(v, β) ≤ θ^en_k`. -/
@[collatz_pos_dens "lem_s02_trace_term"]
theorem exp_gammaStar_mul_rhoStar_pow_lt {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hvb : BkBlack n ξ (epsStar : ℝ) v) {N : ℕ}
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ v + N) (k : ℕ) :
    ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (trMoment n ξ v β.1 (k + 1)) ≤
      ENNReal.ofReal (thetaEn k : ℝ) := by
  rw [tsum_trListWeight_mul_trMoment_eq_trKernel hv hvb hN k]
  exact trKernel_two_le_rhoStar hξ k hv hvb

end CollatzPosDens
