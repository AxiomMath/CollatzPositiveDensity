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
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkClaimStar
public import CollatzPosDens.BlackSet.BkColTop

/-!
# White points next to a triangle

Let `ξ` be a unit, `0 < ε < 1/27`, `Δ ∈ bkFamily n ξ ε` and `w ∈ Δ`. A point `e ∈ bkPoints`
outside `Δ` with `bkJ e ≤ ⌊n/2⌋` and `bkDist e w ≤ 1` is white. Indeed `Δ` is the canonical
triangle of some black point of `bkPoints`, so `not_bkBlack_of_bkDist_le_one` shows that `e` is
not black, and by `isBkWhite_iff_not_bkBlack` a point with `bkJ e ≤ ⌊n/2⌋` which is not black
is white.

## Main results

* `CollatzPosDens.isBkWhite_of_bkDist_le_one`: points of `bkPoints` outside a triangle of
  `bkFamily n ξ ε`, within distance `1` of it and with `bkJ e ≤ ⌊n/2⌋`, are white.
-/

@[expose] public section

namespace CollatzPosDens

/-- **White points next to a triangle.** Let `ξ` be a unit, `0 < ε < 1/27`,
`Δ ∈ bkFamily n ξ ε` and `w ∈ Δ`. If `e ∈ bkPoints`, `e ∉ Δ`, `bkJ e ≤ ⌊n/2⌋` and
`bkDist e w ≤ 1`, then `e` is white. -/
@[collatz_pos_dens "lem_bk_white_near"]
theorem isBkWhite_of_bkDist_le_one {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {Δ : BkTriangle}
    {w e : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hΔ : Δ ∈ bkFamily n ξ ε) (hw : w ∈ Δ) (he : e ∈ bkPoints) (heΔ : e ∉ Δ)
    (hj : bkJ e ≤ ((n / 2 : ℕ) : ℤ)) (hd : bkDist e w ≤ 1) :
    IsBkWhite n ξ ε e := by
  obtain ⟨p, hp, hb, rfl⟩ := hΔ
  have hnb := not_bkBlack_of_bkDist_le_one hξ hε₀ hε hp hb he heΔ hw hd
  exact (isBkWhite_iff_not_bkBlack hj).2 hnb

end CollatzPosDens
