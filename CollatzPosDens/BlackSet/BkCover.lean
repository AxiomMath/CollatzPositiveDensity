/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkBlackOn
public import CollatzPosDens.BlackSet.BkSourceMem

/-!
# The canonical family covers the black set

Let `ξ` be a unit and `0 < ε < 1/27`. A point `p ∈ 𝒫` is black if and only if it lies in
some triangle of the canonical family `𝔗_{n,ξ,ε}`. A black point lies in its own canonical
triangle `Δ(p)`, and conversely every point of a canonical triangle `Δ(p')` at a black `p'` is
black.

## Main results

* `CollatzPosDens.bkBlack_iff_exists_mem_bkFamily`: `p` is black iff `p ∈ Δ` for some
  `Δ ∈ 𝔗_{n,ξ,ε}`.

## Implementation notes

The statement concerns points of `𝒫`, recorded by the hypothesis `p ∈ bkPoints`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **The canonical family covers the black set.** Let `ξ` be a unit and `0 < ε < 1/27`.
A point `p ∈ 𝒫` is black iff `p ∈ Δ` for some triangle `Δ ∈ 𝔗_{n,ξ,ε}`. -/
@[collatz_pos_dens "lem_bk_cover"]
theorem bkBlack_iff_exists_mem_bkFamily {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27) (hp : p ∈ bkPoints) :
    BkBlack n ξ ε p ↔ ∃ Δ ∈ bkFamily n ξ ε, p ∈ Δ := by
  constructor
  · intro hb
    exact ⟨_, bkCanonTriangle_mem_bkFamily hp hb, mem_bkCanonTriangle_self hξ hε₀ hε hp hb⟩
  · rintro ⟨_, ⟨p', hp', hb', rfl⟩, hmem⟩
    exact bkBlack_of_mem_bkCanonTriangle hξ hε₀ hε hp' hb' hmem

end CollatzPosDens
