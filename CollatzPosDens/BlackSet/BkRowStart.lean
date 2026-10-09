/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkColTop

/-!
# The start of a black row run

Fix `n`, `ξ`, `ε` and a point `p = (j, l)`, and let `l_*(p)` be `CollatzPosDens.bkColTop n ξ ε p`,
the top of the run of non-white points above `p`. Then `j_*(p)` is the least integer `a` with
`1 ≤ a ≤ j` such that `(r, l_*(p))` is black for every integer `r` with `a ≤ r ≤ j`; if there
is no such `a`, then `j_*(p) := j`. Thus, when some such `a` exists, the row `l_*(p)` is black
from `j_*(p)` up to `j`, and is not black on all of `[a, j]` for any `1 ≤ a < j_*(p)`.

## Main definitions

* `CollatzPosDens.bkRowStart n ξ ε p`: the value `j_*(p)`.

## Main results

* `CollatzPosDens.bkRowStart_eq_bkJ_of_not_exists`: `j_*(p) = j` when no admissible `a` exists.
* `CollatzPosDens.bkRowStart_spec_of_exists`: the characterization of `j_*(p)` as the least
  admissible `a` when one exists.
* `CollatzPosDens.bkRowStart_le`: `j_*(p) ≤ j`.
* `CollatzPosDens.bkBlack_of_bkRowStart_le_of_le`: the row `l_*(p)` is black on
  `[j_*(p), j]` when an admissible `a` exists.

## Implementation notes

The least `a ≥ 1` is encoded as `a = 1 + s` with `s : ℕ` minimal, obtained by `Nat.find`, so
that `j_*(p) = 1 + s`. The definition is made for every `p : ℤ × ℤ`, not only for black points.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- `j_*(p)` for `p = (j, l)`: the least integer `a` with `1 ≤ a ≤ j` such that
`(r, bkColTop n ξ ε p)` is black for every `a ≤ r ≤ j`, and `j` if there is no such `a`. -/
@[collatz_pos_dens "def_bk_row_start"]
noncomputable def bkRowStart (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : ℤ :=
  open Classical in
  if h : ∃ s : ℕ, (1 + s : ℤ) ≤ bkJ p ∧
      ∀ r : ℤ, 1 + s ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p) then
    1 + Nat.find h
  else bkJ p

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}

private theorem bkRowStart_exists_nat_iff :
    (∃ s : ℕ, (1 + s : ℤ) ≤ bkJ p ∧
      ∀ r : ℤ, 1 + s ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p)) ↔
    ∃ a : ℤ, 1 ≤ a ∧ a ≤ bkJ p ∧
      ∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p) := by
  refine ⟨fun ⟨s, hs, h⟩ ↦ ⟨1 + s, by omega, hs, h⟩,
    fun ⟨a, ha, haj, h⟩ ↦ ⟨(a - 1).toNat, by omega, ?_⟩⟩
  rwa [show (1 + ((a - 1).toNat : ℤ)) = a by omega]

/-- If no `a` with `1 ≤ a ≤ j` makes the row `l_*(p)` black on `[a, j]`, then `j_*(p) = j`. -/
theorem bkRowStart_eq_bkJ_of_not_exists
    (h : ¬∃ a : ℤ, 1 ≤ a ∧ a ≤ bkJ p ∧
      ∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p)) :
    bkRowStart n ξ ε p = bkJ p := by
  rw [← bkRowStart_exists_nat_iff] at h
  rw [bkRowStart, dite_eq_right_of_eq_false (eq_false h)]

/-- Characterization of `j_*(p)` when some admissible `a` exists: `j_*(p)` satisfies
`1 ≤ j_*(p) ≤ j`, the row `l_*(p)` is black on `[j_*(p), j]`, and no `1 ≤ a < j_*(p)` makes the
row black on `[a, j]`. -/
theorem bkRowStart_spec_of_exists
    (h : ∃ a : ℤ, 1 ≤ a ∧ a ≤ bkJ p ∧
      ∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p)) :
    1 ≤ bkRowStart n ξ ε p ∧ bkRowStart n ξ ε p ≤ bkJ p ∧
      (∀ r : ℤ, bkRowStart n ξ ε p ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p)) ∧
      ∀ a : ℤ, 1 ≤ a → a < bkRowStart n ξ ε p →
        ¬∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p) := by
  classical
  rw [← bkRowStart_exists_nat_iff] at h
  have hc : bkRowStart n ξ ε p = 1 + Nat.find h := by
    rw [bkRowStart, dite_eq_left_of_eq_true (eq_true h)]
  have hs := Nat.find_spec h
  refine ⟨by omega, hc ▸ hs.1, hc ▸ hs.2, ?_⟩
  intro a ha hlt hall
  apply Nat.find_min h (show (a - 1).toNat < Nat.find h by omega)
  rw [show (1 + ((a - 1).toNat : ℤ)) = a by omega]
  exact ⟨by omega, hall⟩

/-- `j_*(p) ≤ j`. -/
theorem bkRowStart_le : bkRowStart n ξ ε p ≤ bkJ p := by
  by_cases h : ∃ a : ℤ, 1 ≤ a ∧ a ≤ bkJ p ∧
      ∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p)
  · exact (bkRowStart_spec_of_exists h).2.1
  · exact (bkRowStart_eq_bkJ_of_not_exists h).le

/-- If some admissible `a` exists, then `(r, l_*(p))` is black for `j_*(p) ≤ r ≤ j`. -/
theorem bkBlack_of_bkRowStart_le_of_le
    (h : ∃ a : ℤ, 1 ≤ a ∧ a ≤ bkJ p ∧
      ∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p))
    {r : ℤ} (hr : bkRowStart n ξ ε p ≤ r) (hrj : r ≤ bkJ p) :
    BkBlack n ξ ε (r, bkColTop n ξ ε p) :=
  (bkRowStart_spec_of_exists h).2.2.1 r hr hrj

end CollatzPosDens
