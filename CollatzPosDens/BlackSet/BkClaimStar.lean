/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.BlackSet.BkNeighbourhood
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkRowStart
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkStarCase1
public import CollatzPosDens.BlackSet.BkStarCase2
public import CollatzPosDens.BlackSet.BkStarCase3

/-!
# Claim (*): the cardinal neighbourhood of a canonical triangle contains no black point

Let `ξ` be a unit, `0 < ε < 1/27`, `p` black and `q ∈ 𝒩(Δ(p))`, the cardinal neighbourhood
of the canonical triangle `Δ(p)`. Then `q` is not black.

Exactly one of `j(q) < j_*(p)`; `j(q) ≥ j_*(p)` and `l(q) ≤ l_*(p)`; `j(q) ≥ j_*(p)` and
`l(q) > l_*(p)` holds, and each case is one of the three cases of Claim (*).

## Main results

* `CollatzPosDens.not_bkBlack_of_bkDist_le_one`: Claim (*).

## Implementation notes

Black points are points of `𝒫`; this is recorded by the hypothesis
`p ∈ bkPoints`, needed to form the canonical triangle `Δ(p)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Claim (*).** Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black and `q ∈ 𝒩(Δ(p))`.
Then `q` is not black. -/
@[collatz_pos_dens "lem_bk_claim_star"]
theorem not_bkBlack_of_bkDist_le_one {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {p q : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p)
    (hqN : q ∈ bkNeighbourhood (bkCanonTriangle n ξ ε p hp)) :
    ¬BkBlack n ξ ε q := by
  obtain ⟨hqP, hq, r₀, hr₀, hcard⟩ := hqN
  rcases lt_or_ge (bkJ q) (bkRowStart n ξ ε p) with hj | hj
  · exact not_bkBlack_of_bkJ_lt_bkRowStart hξ hε₀ hε hp hb hqP hr₀ hcard hj
  rcases le_or_gt (bkL q) (bkColTop n ξ ε p) with hl | hl
  · exact not_bkBlack_of_bkRowStart_le_of_le_bkColTop hξ hε₀ (by linarith) hp hb hq hr₀ hcard
      hj hl
  · exact not_bkBlack_of_bkRowStart_le_of_bkColTop_lt hξ hε₀ hε hp hb hq hr₀ hcard hj hl

end CollatzPosDens
