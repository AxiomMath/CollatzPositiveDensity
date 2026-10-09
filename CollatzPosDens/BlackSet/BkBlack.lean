/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkTheta

/-!
# Black points

Fix a level `n`, a residue `ξ : ResidueGroup n` (the group `ℤ/3^nℤ`) and a tolerance `ε`. A
point `p` of the lattice point set `bkPoints = {(j, l) ∈ ℤ × ℤ | 1 ≤ j}` is *black* (for
`n, ξ, ε`) if its first coordinate satisfies `j(p) ≤ ⌊n/2⌋` and its angle `ϑ_{n,ξ}(p)`, given
by `bkTheta`, satisfies `|ϑ_{n,ξ}(p)| ≤ ε`.

## Main definitions

* `CollatzPosDens.BkBlack n ξ ε p`: the point `p` is black for `n, ξ, ε`.

## Main results

* `CollatzPosDens.bkBlack_iff`: the defining characterization.
* `CollatzPosDens.BkBlack.bkJ_le`, `CollatzPosDens.BkBlack.abs_bkTheta_le`: the two conditions.
* `CollatzPosDens.BkBlack.mono`: blackness is monotone in `ε`.
* `CollatzPosDens.not_bkBlack_of_lt`: a point with `|ϑ_{n,ξ}(p)| > ε` is not black.
* `CollatzPosDens.bkBlack_of_half_le`: for `ε ≥ 1/2` the angle condition is automatic.

## Implementation notes

The predicate is defined for every `p : ℤ × ℤ`, not only for `p ∈ bkPoints`. The bound `⌊n/2⌋` is
the natural-number quotient `n / 2`, cast to `ℤ`. A `DecidablePred` instance (classical, through
the order on `ℝ`) is provided.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A point `p` is *black* for `n, ξ, ε` if `j(p) ≤ ⌊n/2⌋` and `|ϑ_{n,ξ}(p)| ≤ ε`. -/
@[collatz_pos_dens "def_bk_black"]
def BkBlack (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : Prop :=
  bkJ p ≤ ((n / 2 : ℕ) : ℤ) ∧ |bkTheta n ξ p| ≤ ε

/-- Unfolding lemma for `BkBlack`. -/
theorem bkBlack_iff {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ} :
    BkBlack n ξ ε p ↔ bkJ p ≤ ((n / 2 : ℕ) : ℤ) ∧ |bkTheta n ξ p| ≤ ε := Iff.rfl

/-- Blackness is decidable (classically, through the order on `ℝ`). -/
noncomputable instance (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) :
    DecidablePred (BkBlack n ξ ε) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A black point has `j(p) ≤ ⌊n/2⌋`. -/
theorem BkBlack.bkJ_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : BkBlack n ξ ε p) : bkJ p ≤ ((n / 2 : ℕ) : ℤ) := h.1

/-- A black point has `|ϑ_{n,ξ}(p)| ≤ ε`. -/
theorem BkBlack.abs_bkTheta_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : BkBlack n ξ ε p) : |bkTheta n ξ p| ≤ ε := h.2

/-- Being black is monotone in the tolerance `ε`. -/
theorem BkBlack.mono {n : ℕ} {ξ : ResidueGroup n} {ε ε' : ℝ} {p : ℤ × ℤ}
    (h : BkBlack n ξ ε p) (hε : ε ≤ ε') : BkBlack n ξ ε' p :=
  ⟨h.1, h.2.trans hε⟩

/-- A point whose angle exceeds `ε` in absolute value is not black. -/
theorem not_bkBlack_of_lt {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : ε < |bkTheta n ξ p|) : ¬BkBlack n ξ ε p :=
  fun hb => (hb.2.trans_lt h).false

/-- For `1 / 2 ≤ ε`, every point with `j(p) ≤ ⌊n/2⌋` is black. -/
theorem bkBlack_of_half_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (hε : 1 / 2 ≤ ε) (hj : bkJ p ≤ ((n / 2 : ℕ) : ℤ)) : BkBlack n ξ ε p :=
  ⟨hj, (abs_bkTheta_le n ξ p).trans hε⟩

end CollatzPosDens
