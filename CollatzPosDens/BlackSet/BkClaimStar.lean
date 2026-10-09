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
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkRowStart
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkStarCase1
public import CollatzPosDens.BlackSet.BkStarCase2
public import CollatzPosDens.BlackSet.BkStarCase3

/-!
# No black point lies next to a canonical triangle

Let `ξ` be a unit, `0 < ε < 1/27`, `p` black and `q ∈ 𝒫` with `q ∉ Δ(p)`. If some
`r₀ ∈ Δ(p)` satisfies `|q - r₀| ≤ 1`, then `q` is not black.

Exactly one of `j(q) < j_*(p)`; `j(q) ≥ j_*(p)` and `l(q) ≤ l_*(p)`; `j(q) ≥ j_*(p)` and
`l(q) > l_*(p)` holds, and these cases are `not_bkBlack_of_bkJ_lt_bkRowStart`,
`not_bkBlack_of_bkRowStart_le_of_le_bkColTop` and `not_bkBlack_of_bkRowStart_le_of_bkColTop_lt`.

## Main results

* `CollatzPosDens.not_bkBlack_of_bkDist_le_one`: a point of `𝒫` outside the canonical triangle
  `Δ(p)` of a black point `p`, at distance at most `1` from `Δ(p)`, is not black.

## Implementation notes

As in the source, black points are points of `𝒫`; this is recorded by the hypothesis
`p ∈ bkPoints`, needed to form the canonical triangle `Δ(p)`.

## References

* [Mazur, §5.5]
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black and `q ∈ 𝒫` with `q ∉ Δ(p)`. If some
`r₀ ∈ Δ(p)` satisfies `|q - r₀| ≤ 1`, then `q` is not black. -/
@[collatz_pos_dens "lem_bk_claim_star"]
theorem not_bkBlack_of_bkDist_le_one {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {p q r₀ : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (hqP : q ∈ bkPoints)
    (hq : q ∉ bkCanonTriangle n ξ ε p hp)
    (hr₀ : r₀ ∈ bkCanonTriangle n ξ ε p hp) (hdist : bkDist q r₀ ≤ 1) :
    ¬BkBlack n ξ ε q := by
  rcases lt_or_ge (bkJ q) (bkRowStart n ξ ε p) with hj | hj
  · exact not_bkBlack_of_bkJ_lt_bkRowStart hξ hε₀ hε hp hb hqP hq hr₀ hdist hj
  rcases le_or_gt (bkL q) (bkColTop n ξ ε p) with hl | hl
  · exact not_bkBlack_of_bkRowStart_le_of_le_bkColTop hξ hε₀ (by linarith) hp hb hq hr₀ hdist
      hj hl
  · exact not_bkBlack_of_bkRowStart_le_of_bkColTop_lt hξ hε₀ hε hp hb hq hr₀ hdist hj hl

end CollatzPosDens
