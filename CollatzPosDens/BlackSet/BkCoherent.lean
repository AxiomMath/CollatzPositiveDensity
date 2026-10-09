/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkRowStart
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkNwClosure
public import CollatzPosDens.BlackSet.BkBlackOn
public import CollatzPosDens.BlackSet.BkCoherentTop
public import CollatzPosDens.BlackSet.BkRowstartSpec

/-!
# Black points of a canonical triangle share it

Let `ξ` be a unit, `0 < ε < 1/27`, `p` black and `q ∈ Δ(p)` black. Then `Δ(q) = Δ(p)`.
By `bkColTop_eq_of_mem_bkCanonTriangle` the column tops agree, `l_*(q) = l_*(p) =: L`. With
`a = j_*(p)`, the characterization `eq_bkRowStart_iff` of the row start applies to `q` and `a`:
`1 ≤ a ≤ j(q)` since `q ∈ Δ(p)`; each `(r, L)` with `a ≤ r ≤ j(q)` lies in `Δ(p)` by
north-west closure, hence is black; and `a = 1` or `(a - 1, L)` is white, by
`eq_bkRowStart_iff` for `p`. So `j_*(q) = a`, the two triangles have the same corner, and the
size of a canonical triangle depends only on its corner.

## Main results

* `CollatzPosDens.bkCanonTriangle_eq_of_mem_bkCanonTriangle`: `Δ(q) = Δ(p)`.

## Implementation notes

Black points are points of `𝒫`; this is recorded by the hypothesis `p ∈ bkPoints`, needed to
form `Δ(p)`. Membership `q ∈ Δ(p)` already gives `q ∈ 𝒫`, which is used to form `Δ(q)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Coherence of canonical triangles.** Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black
and `q ∈ Δ(p)` black. Then `Δ(q) = Δ(p)`. -/
@[collatz_pos_dens "lem_bk_coherent"]
theorem bkCanonTriangle_eq_of_mem_bkCanonTriangle {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {p q : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε : 0 < ε) (hε' : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (hq : q ∈ bkCanonTriangle n ξ ε p hp)
    (hqb : BkBlack n ξ ε q) :
    bkCanonTriangle n ξ ε q (BkTriangle.mem_bkPoints_of_mem hq) =
      bkCanonTriangle n ξ ε p hp := by
  have hqP : q ∈ bkPoints := BkTriangle.mem_bkPoints_of_mem hq
  have htop := bkColTop_eq_of_mem_bkCanonTriangle hξ hε hε' hp hb hq hqb
  obtain ⟨h1, -, -, hcase⟩ := (eq_bkRowStart_iff hp hb (bkRowStart n ξ ε p)).1 rfl
  have hrow : bkRowStart n ξ ε q = bkRowStart n ξ ε p := by
    refine ((eq_bkRowStart_iff hqP hqb _).2 ⟨h1, hq.1, fun r h₁ h₂ => ?_, ?_⟩).symm
    · rw [htop]
      refine bkBlack_of_mem_bkCanonTriangle hξ hε hε' hp hb ?_
      exact BkTriangle.mem_of_mem_of_nw (q' := (r, bkColTop n ξ ε p)) hq h₁ h₂ hq.2.1 le_rfl
    · rwa [htop]
  ext
  · exact hrow
  · exact htop
  · simp only [bkCanonTriangle_s, bkCanonSize_def, hrow, htop]

end CollatzPosDens
