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
public import CollatzPosDens.BlackSet.BkColumnEnds

/-!
# Characterisation of the column top

Let `ξ` be a unit of `ResidueGroup n`, let `ε < 1/4`, and let `p = (j, l) ∈ bkPoints` be black.
Then an integer `L` equals the column top `bkColTop n ξ ε p` if and only if `L ≥ l`, every point
`(j, l'')` with `l ≤ l'' ≤ L` is black, and `(j, L + 1)` is white. Since a black column ends
(some point above `p` in its column is white), `bkColTop n ξ ε p + 1` is the least height above
`p` at which the column turns white, which gives both directions.

## Main results

* `CollatzPosDens.eq_bkColTop_iff`: the characterisation of `bkColTop n ξ ε p`.

## Implementation notes

No lower bound on `ε` is needed. Black points are taken to lie in `bkPoints`, which is recorded
by the hypothesis `p ∈ bkPoints`.
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `ξ` be a unit, `ε < 1/4` and `p = (j, l) ∈ bkPoints` black. Then
`L = bkColTop n ξ ε p` if and only if `L ≥ l`, every point `(j, l'')` with `l ≤ l'' ≤ L` is black,
and `(j, L + 1)` is white. -/
@[collatz_pos_dens "lem_bk_coltop_spec"]
theorem eq_bkColTop_iff {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {ε : ℝ}
    (hε : ε < 1 / 4) {p : ℤ × ℤ} (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (L : ℤ) :
    L = bkColTop n ξ ε p ↔
      bkL p ≤ L ∧ (∀ l'' : ℤ, bkL p ≤ l'' → l'' ≤ L → BkBlack n ξ ε (bkJ p, l'')) ∧
        IsBkWhite n ξ ε (bkJ p, L + 1) := by
  have hex : ∃ t : ℤ, 1 ≤ t ∧ IsBkWhite n ξ ε (bkJ p, bkL p + t) :=
    (exists_isBkWhite_of_bkBlack hξ hε hp hb).imp fun _ h => ⟨h.1, h.2.2⟩
  constructor
  · rintro rfl
    exact ⟨le_bkColTop, fun _ => hb.bkBlack_of_le_of_le_bkColTop, isBkWhite_bkColTop_add_one hex⟩
  · rintro ⟨hlL, hblack, hwhite⟩
    rcases lt_trichotomy L (bkColTop n ξ ε p) with h | h | h
    · exact absurd hwhite (not_isBkWhite_of_lt_of_le_bkColTop (by lia) (by lia))
    · exact h
    · exact absurd (hblack _ (Int.le_add_one le_bkColTop) (by lia))
        (not_bkBlack_of_lt (isBkWhite_bkColTop_add_one hex).2)

end CollatzPosDens
