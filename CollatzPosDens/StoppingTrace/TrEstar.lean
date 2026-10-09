/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Beta
public import CollatzPosDens.StoppingTrace.TrFreshPath

/-!
# The large-triangle event of the fresh law

Fix a level `n ≥ 1`, a residue `ξ ∈ G_n` and an entry point `e ∈ 𝒫`. The event
`E^{*,e} ⊆ 𝒜_n` consists of the fresh atoms `a` whose fresh path meets, at some time
`q ∈ {0, …, P_* - 1}`, a triangle `Δ` of the canonical family `𝔗_{n,ξ,ε_*}` that is large at
time `q`, in the sense that `s_Δ ≥ β_*(q)`:
`E^{*,e} = {a ∈ 𝒜_n : ∃ q < P_*, ∃ Δ ∈ 𝔗_{n,ξ,ε_*}, y^e_q(a) ∈ Δ ∧ s_Δ ≥ β_*(q)}`.

## Main definitions

* `CollatzPosDens.trEStar`: the event `E^{*,e}`.

## Main results

* `CollatzPosDens.mem_trEStar`: the membership criterion.
* `CollatzPosDens.trEStar_subset_trAtoms`: `E^{*,e} ⊆ 𝒜_n`.
* `CollatzPosDens.mem_trEStar_iff_exists_black`: the membership criterion, quantifying over
  the black points of `𝒫` instead of the triangles of `𝔗_{n,ξ,ε_*}`.
* `CollatzPosDens.s_lt_betaStar_of_notMem_trEStar`: outside `E^{*,e}`, every triangle of
  `𝔗_{n,ξ,ε_*}` met by the fresh path at a time `q < P_*` has size `s_Δ < β_*(q)`.

## Implementation notes

The event is a subset of the ambient type `(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n`, carrying the
condition `a ∈ 𝒜_n` explicitly. The hypotheses `n ≥ 1` and `e ∈ 𝒫` play no role in the
definition and are dropped, so `trEStar` is defined for every level `n` and every `e : ℤ × ℤ`.

## References

* [Mazur, *Collatz positive density*], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- The large-triangle event
`E^{*,e} = {a ∈ 𝒜_n : ∃ q ∈ {0, …, P_* - 1}, ∃ Δ ∈ 𝔗_{n,ξ,ε_*}, y^e_q(a) ∈ Δ ∧ s_Δ ≥ β_*(q)}`. -/
@[collatz_pos_dens "def_tr_estar"]
def trEStar (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ ∃ q < pStar, ∃ Δ ∈ bkFamily n ξ (epsStar : ℝ),
    trFreshPath e a q ∈ Δ ∧ (betaStar q : ℝ) ≤ Δ.s}

variable {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)}

/-- Membership in the large-triangle event `E^{*,e}`. -/
theorem mem_trEStar :
    a ∈ trEStar n ξ e ↔ a ∈ trAtoms n ∧ ∃ q < pStar, ∃ Δ ∈ bkFamily n ξ (epsStar : ℝ),
      trFreshPath e a q ∈ Δ ∧ (betaStar q : ℝ) ≤ Δ.s :=
  Iff.rfl

/-- `E^{*,e} ⊆ 𝒜_n`. -/
theorem trEStar_subset_trAtoms (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) :
    trEStar n ξ e ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- Membership in `E^{*,e}`, quantifying over the black points `p ∈ 𝒫` whose canonical
triangle `Δ(p)` is met by the fresh path. -/
theorem mem_trEStar_iff_exists_black :
    a ∈ trEStar n ξ e ↔ a ∈ trAtoms n ∧ ∃ q < pStar, ∃ p, ∃ hp : p ∈ bkPoints,
      BkBlack n ξ (epsStar : ℝ) p ∧
      trFreshPath e a q ∈ bkCanonTriangle n ξ (epsStar : ℝ) p hp ∧
        (betaStar q : ℝ) ≤ (bkCanonTriangle n ξ (epsStar : ℝ) p hp).s := by
  simp only [mem_trEStar, exists_mem_bkFamily (P := fun Δ : BkTriangle ↦ _ ∈ Δ ∧ _ ≤ Δ.s)]

/-- Outside `E^{*,e}`, an atom of `𝒜_n` meets at times `q < P_*` only triangles of
`𝔗_{n,ξ,ε_*}` of size `s_Δ < β_*(q)`. -/
theorem s_lt_betaStar_of_notMem_trEStar (ha : a ∈ trAtoms n) (h : a ∉ trEStar n ξ e) {q : ℕ}
    (hq : q < pStar) {Δ : BkTriangle} (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ))
    (hmem : trFreshPath e a q ∈ Δ) : Δ.s < betaStar q := by
  by_contra hs
  exact h ⟨ha, q, hq, Δ, hΔ, hmem, not_lt.1 hs⟩

end CollatzPosDens
