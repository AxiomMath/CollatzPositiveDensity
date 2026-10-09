/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkSeWeight

/-!
# Triangles in the lattice of points

A *triangle* is a triple `Δ = (j_Δ, l_Δ, s_Δ) ∈ ℤ_{≥1} × ℤ × ℝ`, with corner `(j_Δ, l_Δ)` and
size `s_Δ`. A point `p` *lies in* `Δ`, written `p ∈ Δ`, if `j(p) ≥ j_Δ`, `l(p) ≤ l_Δ` and
`(j(p) - j_Δ) log 9 + (l_Δ - l(p)) log 2 ≤ s_Δ`.

## Main definitions

* `CollatzPosDens.BkTriangle`: a triangle, with corner `(j, l)` and size `s`.
* `CollatzPosDens.BkTriangle.corner`: the corner `(j_Δ, l_Δ)` as a point.
* The `Membership (ℤ × ℤ) BkTriangle` instance: `p ∈ Δ`.

## Main results

* `CollatzPosDens.BkTriangle.mem_iff`: unfolding `p ∈ Δ` to the three inequalities.
* `CollatzPosDens.BkTriangle.mem_iff_bkSe`: the same, with the weight clause read as
  `se(corner Δ, p) ≤ s_Δ`.
* `CollatzPosDens.BkTriangle.mem_bkPoints_of_mem`: a point of a triangle lies in `𝒫`.
* `CollatzPosDens.BkTriangle.corner_mem_iff`: the corner lies in `Δ` iff `0 ≤ s_Δ`.

## Implementation notes

Membership is defined for every `p ∈ ℤ × ℤ` rather than only for `p ∈ 𝒫`; this loses nothing,
since `j(p) ≥ j_Δ ≥ 1` forces `p ∈ 𝒫` (`mem_bkPoints_of_mem`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A triangle `Δ = (j_Δ, l_Δ, s_Δ) ∈ ℤ_{≥1} × ℤ × ℝ`, with corner `(j_Δ, l_Δ)` and size `s_Δ`. -/
@[collatz_pos_dens "def_bk_triangle", ext]
structure BkTriangle where
  /-- The first coordinate `j_Δ` of the corner. -/
  j : ℤ
  /-- The second coordinate `l_Δ` of the corner. -/
  l : ℤ
  /-- The size `s_Δ`. -/
  s : ℝ
  /-- The corner lies in `𝒫`: `j_Δ ≥ 1`. -/
  one_le_j : 1 ≤ j

namespace BkTriangle

/-- A point `p` lies in `Δ` if `j(p) ≥ j_Δ`, `l(p) ≤ l_Δ` and
`(j(p) - j_Δ) log 9 + (l_Δ - l(p)) log 2 ≤ s_Δ`. -/
@[collatz_pos_dens "def_bk_triangle"]
instance instMembership : Membership (ℤ × ℤ) BkTriangle where
  mem Δ p := Δ.j ≤ bkJ p ∧ bkL p ≤ Δ.l ∧
    ((bkJ p - Δ.j : ℤ) : ℝ) * Real.log 9 + ((Δ.l - bkL p : ℤ) : ℝ) * Real.log 2 ≤ Δ.s

/-- The corner `(j_Δ, l_Δ)` of a triangle, as a point. -/
def corner (Δ : BkTriangle) : ℤ × ℤ := (Δ.j, Δ.l)

variable {Δ : BkTriangle} {p : ℤ × ℤ}

/-- A point `p` lies in `Δ` iff `j(p) ≥ j_Δ`, `l(p) ≤ l_Δ` and
`(j(p) - j_Δ) log 9 + (l_Δ - l(p)) log 2 ≤ s_Δ`. -/
theorem mem_iff : p ∈ Δ ↔ Δ.j ≤ bkJ p ∧ bkL p ≤ Δ.l ∧
    ((bkJ p - Δ.j : ℤ) : ℝ) * Real.log 9 + ((Δ.l - bkL p : ℤ) : ℝ) * Real.log 2 ≤ Δ.s :=
  Iff.rfl

/-- A point of `Δ` satisfies `j_Δ ≤ j(p)`. -/
theorem j_le_of_mem (h : p ∈ Δ) : Δ.j ≤ bkJ p := h.1

/-- A point of `Δ` satisfies `l(p) ≤ l_Δ`. -/
theorem le_l_of_mem (h : p ∈ Δ) : bkL p ≤ Δ.l := h.2.1

/-- A point of `Δ` satisfies `(j(p) - j_Δ) log 9 + (l_Δ - l(p)) log 2 ≤ s_Δ`. -/
theorem weight_le_of_mem (h : p ∈ Δ) :
    ((bkJ p - Δ.j : ℤ) : ℝ) * Real.log 9 + ((Δ.l - bkL p : ℤ) : ℝ) * Real.log 2 ≤ Δ.s :=
  h.2.2

/-- A point `p` lies in `Δ` iff `j(p) ≥ j_Δ`, `l(p) ≤ l_Δ` and `se((j_Δ, l_Δ), p) ≤ s_Δ`. -/
theorem mem_iff_bkSe : p ∈ Δ ↔ Δ.j ≤ bkJ p ∧ bkL p ≤ Δ.l ∧ bkSe Δ.corner p ≤ Δ.s :=
  Iff.rfl

/-- A point `p` of `Δ` has `se((j_Δ, l_Δ), p) ≤ s_Δ`. -/
theorem bkSe_corner_le_of_mem (h : p ∈ Δ) : bkSe Δ.corner p ≤ Δ.s :=
  h.2.2

/-- A point of a triangle lies in `𝒫`. -/
theorem mem_bkPoints_of_mem (h : p ∈ Δ) : p ∈ bkPoints :=
  mem_bkPoints.2 (Δ.one_le_j.trans h.1)

/-- The first coordinate of the corner of `Δ` is `j_Δ`. -/
@[simp]
theorem corner_fst (Δ : BkTriangle) : Δ.corner.1 = Δ.j := rfl

/-- The second coordinate of the corner of `Δ` is `l_Δ`. -/
@[simp]
theorem corner_snd (Δ : BkTriangle) : Δ.corner.2 = Δ.l := rfl

/-- The corner of a triangle lies in `𝒫`. -/
theorem corner_mem_bkPoints (Δ : BkTriangle) : Δ.corner ∈ bkPoints := Δ.one_le_j

/-- The corner of a triangle lies in it iff its size is nonnegative. -/
@[simp]
theorem corner_mem_iff : Δ.corner ∈ Δ ↔ 0 ≤ Δ.s := by
  simp [mem_iff, corner]

/-- If `Δ` and `Δ'` have the same corner and `s_Δ ≤ s_Δ'`, then every point of `Δ` lies
in `Δ'`. -/
theorem mem_of_mem_of_s_le {Δ' : BkTriangle} (hj : Δ.j = Δ'.j) (hl : Δ.l = Δ'.l)
    (hs : Δ.s ≤ Δ'.s) (h : p ∈ Δ) : p ∈ Δ' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨hj ▸ h1, hl ▸ h2, hj ▸ hl ▸ h3.trans hs⟩

end BkTriangle

end CollatzPosDens
