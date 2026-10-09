/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkWhite

/-!
# The top of a black column run

Fix `n`, `ξ`, `ε` and a point `p = (j, l)`. Let `t ≥ 1` be the least integer such that
`(j, l + t)` is white. Then `l_*(p) := l + t - 1` is the top of the run of non-white points in
column `j` starting directly above `p`; if no point `(j, l + t)` with `t ≥ 1` is white, then
`l_*(p) := l`. For a black point `p` every point `(j, m)` with `l ≤ m ≤ l_*(p)` is black.

## Main definitions

* `CollatzPosDens.bkColTop n ξ ε p`: the value `l_*(p)`.

## Main results

* `CollatzPosDens.bkColTop_of_not_exists`: `l_*(p) = l` when no white point lies above `p`.
* `CollatzPosDens.le_bkColTop`: `l ≤ l_*(p)`.
* `CollatzPosDens.isBkWhite_bkColTop_add_one`: `(j, l_*(p) + 1)` is white when some white point
  lies above `p`.
* `CollatzPosDens.not_isBkWhite_of_lt_of_le_bkColTop`: `(j, m)` is not white for
  `l < m ≤ l_*(p)`.
* `CollatzPosDens.isBkWhite_iff_not_bkBlack`: for `j(p) ≤ ⌊n/2⌋`, `p` is white iff it is not
  black.
* `CollatzPosDens.BkBlack.bkBlack_of_le_of_le_bkColTop`: if `p` is black, then `(j, m)` is
  black for `l ≤ m ≤ l_*(p)`.

## Implementation notes

The least `t ≥ 1` is encoded as `t = s + 1` with `s : ℕ` minimal, obtained by `Nat.find`, so that
`l_*(p) = l + s`. The definition is made for every `p : ℤ × ℤ`, not only for black points.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- `l_*(p) := l + t - 1` where `t ≥ 1` is least with `(j, l + t)` white, and `l_*(p) := l`
if there is no such `t`. Here `p = (j, l)`. -/
@[collatz_pos_dens "def_bk_col_top"]
noncomputable def bkColTop (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : ℤ :=
  open Classical in
  if h : ∃ s : ℕ, IsBkWhite n ξ ε (bkJ p, bkL p + (s + 1)) then bkL p + Nat.find h else bkL p

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}

/-- If no point `(j, l + t)`, `t ≥ 1`, is white, then `l_*(p) = l`. -/
theorem bkColTop_of_not_exists (h : ¬∃ t : ℤ, 1 ≤ t ∧ IsBkWhite n ξ ε (bkJ p, bkL p + t)) :
    bkColTop n ξ ε p = bkL p := by
  have h' : ¬∃ s : ℕ, IsBkWhite n ξ ε (bkJ p, bkL p + (s + 1)) := fun ⟨s, hs⟩ =>
    h ⟨s + 1, by omega, by exact_mod_cast hs⟩
  rw [bkColTop, dite_eq_right_of_eq_false (eq_false h')]

/-- Characterization of `l_*(p)` when some point above `p` in its column is white: `l_*(p) + 1`
is the least `l + t`, `t ≥ 1`, with `(j, l + t)` white. -/
theorem bkColTop_spec_of_exists (h : ∃ t : ℤ, 1 ≤ t ∧ IsBkWhite n ξ ε (bkJ p, bkL p + t)) :
    bkL p ≤ bkColTop n ξ ε p ∧ IsBkWhite n ξ ε (bkJ p, bkColTop n ξ ε p + 1) ∧
      ∀ m, bkL p < m → m ≤ bkColTop n ξ ε p → ¬IsBkWhite n ξ ε (bkJ p, m) := by
  classical
  have h' : ∃ s : ℕ, IsBkWhite n ξ ε (bkJ p, bkL p + (s + 1)) := by
    obtain ⟨t, ht, hw⟩ := h
    refine ⟨(t - 1).toNat, ?_⟩
    have : ((t - 1).toNat : ℤ) + 1 = t := by omega
    rwa [this]
  have hc : bkColTop n ξ ε p = bkL p + Nat.find h' := by
    rw [bkColTop, dite_eq_left_of_eq_true (eq_true h')]
  refine ⟨by omega, ?_, ?_⟩
  · have := Nat.find_spec h'
    rw [hc, add_assoc]
    exact this
  · intro m hm hmt hw
    have hlt : (m - bkL p - 1).toNat < Nat.find h' := by omega
    apply Nat.find_min h' hlt
    have : bkL p + (((m - bkL p - 1).toNat : ℕ) + 1 : ℤ) = m := by omega
    rwa [this]

/-- `l ≤ l_*(p)`. -/
theorem le_bkColTop : bkL p ≤ bkColTop n ξ ε p := by
  by_cases h : ∃ t : ℤ, 1 ≤ t ∧ IsBkWhite n ξ ε (bkJ p, bkL p + t)
  · exact (bkColTop_spec_of_exists h).1
  · exact (bkColTop_of_not_exists h).ge

/-- If some point above `p` in its column is white, then `(j, l_*(p) + 1)` is white. -/
theorem isBkWhite_bkColTop_add_one
    (h : ∃ t : ℤ, 1 ≤ t ∧ IsBkWhite n ξ ε (bkJ p, bkL p + t)) :
    IsBkWhite n ξ ε (bkJ p, bkColTop n ξ ε p + 1) :=
  (bkColTop_spec_of_exists h).2.1

/-- No point `(j, m)` with `l < m ≤ l_*(p)` is white. -/
theorem not_isBkWhite_of_lt_of_le_bkColTop {m : ℤ} (hlm : bkL p < m)
    (hm : m ≤ bkColTop n ξ ε p) : ¬IsBkWhite n ξ ε (bkJ p, m) := by
  by_cases h : ∃ t : ℤ, 1 ≤ t ∧ IsBkWhite n ξ ε (bkJ p, bkL p + t)
  · exact (bkColTop_spec_of_exists h).2.2 m hlm hm
  · rw [bkColTop_of_not_exists h] at hm
    omega

/-- In the strip `j(p) ≤ ⌊n/2⌋`, a point is white iff it is not black. -/
theorem isBkWhite_iff_not_bkBlack (hj : bkJ p ≤ ((n / 2 : ℕ) : ℤ)) :
    IsBkWhite n ξ ε p ↔ ¬BkBlack n ξ ε p :=
  ⟨fun hw hb => (hb.2.trans_lt hw.2).false, fun hb => ⟨hj, lt_of_not_ge fun h => hb ⟨hj, h⟩⟩⟩

/-- If `p = (j, l)` is black, then every point `(j, m)` with `l ≤ m ≤ l_*(p)` is black. -/
theorem BkBlack.bkBlack_of_le_of_le_bkColTop (hp : BkBlack n ξ ε p) {m : ℤ} (hlm : bkL p ≤ m)
    (hm : m ≤ bkColTop n ξ ε p) : BkBlack n ξ ε (bkJ p, m) := by
  rcases hlm.lt_or_eq with hlm | rfl
  · have hw := not_isBkWhite_of_lt_of_le_bkColTop hlm hm
    exact not_not.1 fun hb => hw ((isBkWhite_iff_not_bkBlack (p := (bkJ p, m)) hp.1).2 hb)
  · exact hp

end CollatzPosDens
