/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkNwClosure
public import CollatzPosDens.BlackSet.BkBlackOn
public import CollatzPosDens.BlackSet.BkClaimStar
public import CollatzPosDens.BlackSet.BkColtopSpec
public import CollatzPosDens.BlackSet.BkNeighbourhood
public import CollatzPosDens.BlackSet.BkCardinal

/-!
# Black points of a canonical triangle share its column top

Let `ξ` be a unit, `0 < ε < 1/27`, `p` black and `q ∈ Δ(p)` black. Then `l_*(q) = l_*(p)`.

Put `L = l_*(p)`, the second corner coordinate of `Δ(p)`, and check the characterisation of the
column top for `q` and `L`: first `l(q) ≤ L` since `q ∈ Δ(p)`; next each `(j(q), l'')` with
`l(q) ≤ l'' ≤ L` lies in `Δ(p)` by north-west closure, hence is black; finally
`(j(q), L + 1)` lies outside `Δ(p)` and is a cardinal neighbour of `(j(q), L) ∈ Δ(p)`, so it lies
in `𝒩(Δ(p))` and is not black by Claim (*), and since `j(q) ≤ ⌊n/2⌋` it is white.

## Main results

* `CollatzPosDens.bkColTop_eq_of_mem_bkCanonTriangle`: `l_*(q) = l_*(p)`.

## Implementation notes

Black points are points of `𝒫`; this is recorded by the hypothesis `p ∈ bkPoints`, needed to form
the canonical triangle `Δ(p)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Coherence of the column top.** Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black and
`q ∈ Δ(p)` black. Then `l_*(q) = l_*(p)`. -/
@[collatz_pos_dens "lem_bk_coherent_top"]
theorem bkColTop_eq_of_mem_bkCanonTriangle {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {p q : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε : 0 < ε) (hε' : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (hq : q ∈ bkCanonTriangle n ξ ε p hp)
    (hqb : BkBlack n ξ ε q) : bkColTop n ξ ε q = bkColTop n ξ ε p := by
  set Δ := bkCanonTriangle n ξ ε p hp
  have hqP : q ∈ bkPoints := BkTriangle.mem_bkPoints_of_mem hq
  have hL : Δ.l = bkColTop n ξ ε p := rfl
  have hcol : ∀ l'' : ℤ, bkL q ≤ l'' → l'' ≤ Δ.l → (bkJ q, l'') ∈ Δ := fun l'' h₁ h₂ =>
    BkTriangle.mem_of_mem_of_nw (q' := (bkJ q, l'')) hq hq.1 le_rfl h₁ h₂
  refine ((eq_bkColTop_iff hξ (by linarith) hqP hqb (bkColTop n ξ ε p)).2
    ⟨BkTriangle.le_l_of_mem hq, fun l'' h₁ h₂ =>
      bkBlack_of_mem_bkCanonTriangle hξ hε hε' hp hb (hcol l'' h₁ h₂), ?_⟩).symm
  have hy : (bkJ q, bkColTop n ξ ε p + 1) ∉ Δ := fun h => by
    have := BkTriangle.le_l_of_mem h
    simp only [bkL] at this
    omega
  exact (isBkWhite_iff_not_bkBlack (p := (bkJ q, bkColTop n ξ ε p + 1)) hqb.bkJ_le).2
    (not_bkBlack_of_bkDist_le_one (q := (bkJ q, bkColTop n ξ ε p + 1)) hξ hε hε' hp hb
      (mem_bkNeighbourhood_of (mem_bkPoints.2 (mem_bkPoints.1 hqP)) hy
        (hcol Δ.l (BkTriangle.le_l_of_mem hq) le_rfl)
        (by simp [BkCardinalNeighbour, bkJ, bkL, hL])))

end CollatzPosDens
