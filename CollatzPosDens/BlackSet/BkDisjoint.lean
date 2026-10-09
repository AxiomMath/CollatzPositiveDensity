/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkBlackOn
public import CollatzPosDens.BlackSet.BkCoherent

/-!
# The canonical triangles are pairwise disjoint

Let `ξ` be a unit and `0 < ε < 1/27`. Two triangles `Δ, Γ` of the canonical family
`𝔗_{n,ξ,ε}` that share a point are equal. Writing `Δ = Δ(p)` and `Γ = Δ(p')` with `p, p'`
black, a common point `x` is black since it lies in `Δ(p)`, and coherence of canonical
triangles gives `Δ(x) = Δ(p)` and `Δ(x) = Δ(p')`.

## Main results

* `CollatzPosDens.eq_of_mem_bkFamily_of_mem`: two members of `𝔗` with a common point are
  equal.
* `CollatzPosDens.pairwiseDisjoint_bkFamily`: the family `𝔗`, viewed as a family of point
  sets, is pairwise disjoint.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The canonical family is disjoint.** Let `ξ` be a unit and `0 < ε < 1/27`. If
`Δ, Γ ∈ 𝔗_{n,ξ,ε}` and some point `x` lies in both, then `Δ = Γ`. -/
@[collatz_pos_dens "lem_bk_disjoint"]
theorem eq_of_mem_bkFamily_of_mem {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {Δ Γ : BkTriangle}
    {x : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε : 0 < ε) (hε' : ε < 1 / 27)
    (hΔ : Δ ∈ bkFamily n ξ ε) (hΓ : Γ ∈ bkFamily n ξ ε) (hxΔ : x ∈ Δ) (hxΓ : x ∈ Γ) :
    Δ = Γ := by
  obtain ⟨p, hp, hb, rfl⟩ := hΔ
  obtain ⟨p', hp', hb', rfl⟩ := hΓ
  have hxb : BkBlack n ξ ε x := bkBlack_of_mem_bkCanonTriangle hξ hε hε' hp hb hxΔ
  rw [← bkCanonTriangle_eq_of_mem_bkCanonTriangle hξ hε hε' hp hb hxΔ hxb,
    ← bkCanonTriangle_eq_of_mem_bkCanonTriangle hξ hε hε' hp' hb' hxΓ hxb]

/-- Let `ξ` be a unit and `0 < ε < 1/27`. The canonical family `𝔗_{n,ξ,ε}` is pairwise
disjoint as a family of point sets. -/
theorem pairwiseDisjoint_bkFamily {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hξ : IsResidueUnit ξ) (hε : 0 < ε) (hε' : ε < 1 / 27) :
    (bkFamily n ξ ε).PairwiseDisjoint fun Δ : BkTriangle => {x : ℤ × ℤ | x ∈ Δ} :=
  fun _ hΔ _ hΓ hne => Set.disjoint_left.2 fun _ hxΔ hxΓ =>
    hne (eq_of_mem_bkFamily_of_mem hξ hε hε' hΔ hΓ hxΔ hxΓ)

end CollatzPosDens
