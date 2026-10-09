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

/-!
# Black points of a canonical triangle share its column top

Let `ξ` be a unit, `0 < ε < 1/27`, `p` black and `q ∈ Δ(p)` black, where `Δ(p)` is the
canonical triangle of `p`. Then the column tops agree: `l_*(q) = l_*(p)`.

## Main results

* `CollatzPosDens.bkColTop_eq_of_mem_bkCanonTriangle`: `l_*(q) = l_*(p)`.

## Implementation notes

As in the source, black points are points of `𝒫`; this is recorded by the hypothesis
`p ∈ bkPoints`, needed to form the canonical triangle `Δ(p)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.6.
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
    ⟨?_, ?_, ?_⟩).symm
  · exact BkTriangle.le_l_of_mem hq
  · intro l'' h₁ h₂
    exact bkBlack_of_mem_bkCanonTriangle hξ hε hε' hp hb (hcol l'' h₁ h₂)
  · have hr₀ : (bkJ q, Δ.l) ∈ Δ := hcol Δ.l (BkTriangle.le_l_of_mem hq) le_rfl
    have hy : (bkJ q, bkColTop n ξ ε p + 1) ∉ Δ := fun h => by
      have := BkTriangle.le_l_of_mem h
      simp only [bkL] at this
      omega
    have hdist : bkDist (bkJ q, bkColTop n ξ ε p + 1) (bkJ q, Δ.l) ≤ 1 :=
      (bkDist_add_one_snd _ _).le
    have hnb := not_bkBlack_of_bkDist_le_one (q := (bkJ q, bkColTop n ξ ε p + 1))
      hξ hε hε' hp hb (mem_bkPoints.2 (mem_bkPoints.1 hqP)) hy hr₀ hdist
    exact (isBkWhite_iff_not_bkBlack (p := (bkJ q, bkColTop n ξ ε p + 1)) hqb.bkJ_le).2 hnb

end CollatzPosDens
