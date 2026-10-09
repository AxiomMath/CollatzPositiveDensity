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
# White points

Fix a level `n`, a residue `ξ ∈ G_n = ℤ/3^nℤ` and a threshold `ε`. A point `p ∈ 𝒫` is *white*
(for `n, ξ, ε`) if its first coordinate satisfies `j(p) ≤ ⌊n/2⌋` and its angle satisfies
`|ϑ_{n,ξ}(p)| > ε`.

## Main definitions

* `CollatzPosDens.IsBkWhite n ξ ε p`: the point `p` is white for `n, ξ, ε`.

## Main results

* `CollatzPosDens.isBkWhite_iff`: `p` is white iff `j(p) ≤ ⌊n/2⌋` and `|ϑ_{n,ξ}(p)| > ε`.
* `CollatzPosDens.not_isBkWhite_of_half_le`: no point is white once `ε ≥ 1/2`.

## Implementation notes

The predicate is defined for every `p : ℤ × ℤ`, not only for `p ∈ 𝒫`, as the angle `bkTheta`
is; on `𝒫` it agrees with the source. The floor `⌊n/2⌋` of the natural number `n` is the
natural-number division `n / 2`, cast to `ℤ`.

## References

* [Mazur, *Collatz positive density*, §5.1]
-/

@[expose] public section

namespace CollatzPosDens

/-- A point `p` is *white* for `n, ξ, ε` if `j(p) ≤ ⌊n/2⌋` and `|ϑ_{n,ξ}(p)| > ε`. -/
@[collatz_pos_dens "def_bk_white"]
def IsBkWhite (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : Prop :=
  bkJ p ≤ ((n / 2 : ℕ) : ℤ) ∧ ε < |bkTheta n ξ p|

/-- A point `p` is white for `n, ξ, ε` if and only if `j(p) ≤ ⌊n/2⌋` and `|ϑ_{n,ξ}(p)| > ε`. -/
theorem isBkWhite_iff {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ} :
    IsBkWhite n ξ ε p ↔ bkJ p ≤ ((n / 2 : ℕ) : ℤ) ∧ ε < |bkTheta n ξ p| :=
  Iff.rfl

/-- Whiteness for `n, ξ, ε` is a decidable predicate on points. -/
noncomputable instance (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) :
    DecidablePred (IsBkWhite n ξ ε) := fun _ => by
  unfold IsBkWhite; infer_instance

/-- A white point has first coordinate at most `⌊n/2⌋`. -/
theorem IsBkWhite.bkJ_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : IsBkWhite n ξ ε p) : bkJ p ≤ ((n / 2 : ℕ) : ℤ) :=
  h.1

/-- A white point has angle of absolute value greater than `ε`. -/
theorem IsBkWhite.lt_abs_bkTheta {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (h : IsBkWhite n ξ ε p) : ε < |bkTheta n ξ p| :=
  h.2

/-- Whiteness is antitone in the threshold `ε`. -/
theorem IsBkWhite.mono {n : ℕ} {ξ : ResidueGroup n} {ε ε' : ℝ} {p : ℤ × ℤ}
    (h : IsBkWhite n ξ ε p) (hε : ε' ≤ ε) : IsBkWhite n ξ ε' p :=
  ⟨h.1, hε.trans_lt h.2⟩

/-- No point is white once `ε ≥ 1/2`, since `|ϑ_{n,ξ}(p)| ≤ 1/2`. -/
theorem not_isBkWhite_of_half_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} (hε : 1 / 2 ≤ ε)
    (p : ℤ × ℤ) : ¬ IsBkWhite n ξ ε p := fun h =>
  not_lt_of_ge (abs_bkTheta_le n ξ p) (hε.trans_lt h.2)

end CollatzPosDens
