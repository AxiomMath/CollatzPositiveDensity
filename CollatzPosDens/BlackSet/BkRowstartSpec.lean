/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.BlackSet.BkRowStart
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# Characterization of the row start

Let `p = (j, l) ∈ 𝒫` be black. Then an integer `a` equals the row start `j_*(p)` if and only if
`1 ≤ a ≤ j`, every point `(r, l_*(p))` with `a ≤ r ≤ j` is black, and either `a = 1` or
`(a - 1, l_*(p))` is white. Since `(j, l_*(p))` is black, `a = j` is admissible in the definition
of `j_*(p)`, so `j_*(p)` is the least admissible `a`; a point `(a - 1, l_*(p))` with
`a - 1 ≤ j ≤ ⌊n/2⌋` that is not black is white, which gives both directions.

## Main results

* `CollatzPosDens.eq_bkRowStart_iff`: the characterization of `j_*(p)`.

## Implementation notes

The hypotheses that `ξ` is a unit and `0 ≤ ε < 1/4`, assumed in [mazur2026], are not needed:
the argument only uses `p ∈ 𝒫` (so that `j ≥ 1`) and that `p` is black, since `(j, l_*(p))` is
black directly from the definition of `l_*(p)`. Black points are points of `𝒫`, which is
recorded by the hypothesis `p ∈ bkPoints`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Characterization of `j_*(p)`.** Let `p = (j, l) ∈ 𝒫` be black. Then `a = j_*(p)` if and
only if `1 ≤ a ≤ j`, every point `(r, l_*(p))` with `a ≤ r ≤ j` is black, and either `a = 1` or
`(a - 1, l_*(p))` is white. -/
@[collatz_pos_dens "lem_bk_rowstart_spec"]
theorem eq_bkRowStart_iff {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (a : ℤ) :
    a = bkRowStart n ξ ε p ↔
      1 ≤ a ∧ a ≤ bkJ p ∧
        (∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p)) ∧
        (a = 1 ∨ IsBkWhite n ξ ε (a - 1, bkColTop n ξ ε p)) := by
  have hj : 1 ≤ bkJ p := hp
  have hex : ∃ a : ℤ, 1 ≤ a ∧ a ≤ bkJ p ∧
      ∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p) := by
    refine ⟨bkJ p, hj, le_rfl, fun r h₁ h₂ => ?_⟩
    obtain rfl : r = bkJ p := le_antisymm h₂ h₁
    exact hb.bkBlack_of_le_of_le_bkColTop le_bkColTop le_rfl
  obtain ⟨h1, hle, hall, hmin⟩ := bkRowStart_spec_of_exists hex
  have hjn := hb.bkJ_le
  constructor
  · rintro rfl
    refine ⟨h1, hle, hall, ?_⟩
    rcases h1.eq_or_lt with h | h
    · exact Or.inl h.symm
    · refine Or.inr ⟨?_, ?_⟩
      · change bkRowStart n ξ ε p - 1 ≤ _
        omega
      · by_contra hθ
        refine hmin (bkRowStart n ξ ε p - 1) (by omega) (by omega) fun r h₁ h₂ => ?_
        rcases h₁.eq_or_lt with rfl | h₁
        · exact ⟨by change _ - 1 ≤ _; omega, le_of_not_gt hθ⟩
        · exact hall r (by omega) h₂
  · rintro ⟨ha1, haj, hblack, hcase⟩
    rcases lt_trichotomy a (bkRowStart n ξ ε p) with h | h | h
    · exact absurd hblack (hmin a ha1 h)
    · exact h
    · rcases hcase with rfl | hw
      · omega
      · exact absurd (hall (a - 1) (by omega) (by omega)) (not_bkBlack_of_lt hw.2)

end CollatzPosDens
