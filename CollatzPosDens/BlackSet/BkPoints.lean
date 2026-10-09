/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CollatzPosDens.Attr

/-!
# Lattice points

This file defines the lattice point set `𝒫 = ℤ_{≥1} × ℤ`. A point `p = (j, l)` has coordinates
`j(p) = j` and `l(p) = l`; points are added coordinatewise whenever the sum lies in `𝒫`, and
`|p - q| = ((j(p) - j(q))² + (l(p) - l(q))²)^{1/2}` is the Euclidean distance.

## Main definitions

* `CollatzPosDens.bkPoints`: the set `𝒫 = {(j, l) ∈ ℤ × ℤ | 1 ≤ j}`.
* `CollatzPosDens.bkJ`, `CollatzPosDens.bkL`: the coordinates `j(p)` and `l(p)`.
* `CollatzPosDens.bkDistSq`: the squared distance `|p - q|²`, an integer.
* `CollatzPosDens.bkDist`: the Euclidean distance `|p - q|`.
* `CollatzPosDens.bkPointsEquiv`: the parametrization `ℕ × ℤ ≃ 𝒫`, `(m, l) ↦ (m + 1, l)`.
* `CollatzPosDens.natPointsEquiv`: the same parametrization of `{p : ℕ × ℤ // 1 ≤ p.1}`.

## Main results

* `CollatzPosDens.add_mem_bkPoints_iff`: a coordinatewise sum lies in `𝒫` iff its first
  coordinate is at least `1`.
* `CollatzPosDens.bkDist_sq`: `|p - q|² = bkDistSq p q`.
* `CollatzPosDens.natCast_prod_injective`: the cast `ℕ × ℤ → ℤ × ℤ` is injective.
* `CollatzPosDens.bkL_list_sum`: `l(p₁ + ⋯ + p_k) = l(p₁) + ⋯ + l(p_k)`.

## Implementation notes

`𝒫` is a subset of `ℤ × ℤ` rather than a type of its own, since points are compared with, added
to and subtracted from elements of `ℤ × ℤ`: addition is the addition of `ℤ × ℤ`, and "the sum
lies in `𝒫`" is membership in `bkPoints`. The coordinates and the distance are defined on all of
`ℤ × ℤ`, not only on `𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The lattice point set `𝒫 = ℤ_{≥1} × ℤ`, as a subset of `ℤ × ℤ`. -/
@[collatz_pos_dens "def_bk_points"]
def bkPoints : Set (ℤ × ℤ) := {p | 1 ≤ p.1}

/-- The first coordinate `j(p)` of a point `p = (j, l)`. -/
@[collatz_pos_dens "def_bk_points"]
abbrev bkJ (p : ℤ × ℤ) : ℤ := p.1

/-- The second coordinate `l(p)` of a point `p = (j, l)`. -/
@[collatz_pos_dens "def_bk_points"]
abbrev bkL (p : ℤ × ℤ) : ℤ := p.2

/-- The squared Euclidean distance `(j(p) - j(q))² + (l(p) - l(q))²` between two points. -/
@[collatz_pos_dens "def_bk_points"]
def bkDistSq (p q : ℤ × ℤ) : ℤ := (bkJ p - bkJ q) ^ 2 + (bkL p - bkL q) ^ 2

/-- The Euclidean distance `|p - q| = ((j(p) - j(q))² + (l(p) - l(q))²)^{1/2}`. -/
@[collatz_pos_dens "def_bk_points"]
noncomputable def bkDist (p q : ℤ × ℤ) : ℝ := √(bkDistSq p q : ℝ)

/-- A point lies in `𝒫` iff its first coordinate is at least `1`. -/
@[simp]
theorem mem_bkPoints {p : ℤ × ℤ} : p ∈ bkPoints ↔ 1 ≤ bkJ p := Iff.rfl

/-- The point `(j, l)` lies in `𝒫` iff `1 ≤ j`. -/
theorem mem_bkPoints_mk {j l : ℤ} : (j, l) ∈ bkPoints ↔ 1 ≤ j := Iff.rfl

/-- A coordinatewise sum of points lies in `𝒫` iff its first coordinate is at least `1`. -/
theorem add_mem_bkPoints_iff {p q : ℤ × ℤ} : p + q ∈ bkPoints ↔ 1 ≤ bkJ p + bkJ q := Iff.rfl

/-- `ℕ × ℤ` parametrizes `𝒫` via `(m, l) ↦ (m + 1, l)`. -/
def bkPointsEquiv : ℕ × ℤ ≃ bkPoints where
  toFun x := ⟨((x.1 : ℤ) + 1, x.2), by rw [mem_bkPoints_mk]; omega⟩
  invFun p := ((p.1.1 - 1).toNat, p.1.2)
  left_inv x := by simp
  right_inv := by
    rintro ⟨⟨j, l⟩, hj⟩
    rw [mem_bkPoints_mk] at hj
    ext <;> simp; omega

/-- `ℕ × ℤ` parametrizes the pairs `(j, l) : ℕ × ℤ` with `1 ≤ j` via `(m, l) ↦ (m + 1, l)`. -/
def natPointsEquiv : ℕ × ℤ ≃ {p : ℕ × ℤ // 1 ≤ p.1} where
  toFun x := ⟨(x.1 + 1, x.2), by simp⟩
  invFun p := (p.1.1 - 1, p.1.2)
  left_inv x := by simp
  right_inv p := by
    obtain ⟨⟨j, l⟩, hj⟩ := p
    ext <;> simp only; omega

/-- The first coordinate of a sum of points is the sum of their first coordinates. -/
theorem bkJ_list_sum (L : List (ℤ × ℤ)) : bkJ L.sum = (L.map bkJ).sum :=
  map_list_sum (AddMonoidHom.fst ℤ ℤ) L

/-- The second coordinate of a sum of points is the sum of their second coordinates. -/
theorem bkL_list_sum (L : List (ℤ × ℤ)) : bkL L.sum = (L.map bkL).sum :=
  map_list_sum (AddMonoidHom.snd ℤ ℤ) L

/-- The coordinatewise cast `ℕ × ℤ → ℤ × ℤ`, `(m, l) ↦ (m, l)`, is injective. -/
theorem natCast_prod_injective : Function.Injective fun x : ℕ × ℤ ↦ ((x.1 : ℤ), x.2) :=
  Nat.cast_injective.prodMap Function.injective_id

/-- The sum of two points of `𝒫` lies in `𝒫`. -/
theorem add_mem_bkPoints {p q : ℤ × ℤ} (hp : p ∈ bkPoints) (hq : q ∈ bkPoints) :
    p + q ∈ bkPoints := by
  simp only [mem_bkPoints, bkJ, Prod.fst_add] at *
  omega

/-- The squared distance is nonnegative. -/
theorem bkDistSq_nonneg (p q : ℤ × ℤ) : 0 ≤ bkDistSq p q := by
  unfold bkDistSq; positivity

/-- The squared distance is symmetric. -/
theorem bkDistSq_comm (p q : ℤ × ℤ) : bkDistSq p q = bkDistSq q p := by
  unfold bkDistSq; ring

/-- The squared distance from a point to itself is zero. -/
@[simp]
theorem bkDistSq_self (p : ℤ × ℤ) : bkDistSq p p = 0 := by
  simp [bkDistSq]

/-- The squared distance between `p` and `q` vanishes iff `p = q`. -/
@[simp]
theorem bkDistSq_eq_zero_iff {p q : ℤ × ℤ} : bkDistSq p q = 0 ↔ p = q := by
  refine ⟨fun h => ?_, fun h => h ▸ bkDistSq_self p⟩
  unfold bkDistSq at h
  obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h
  exact Prod.ext (by simpa [sub_eq_zero] using h1) (by simpa [sub_eq_zero] using h2)

/-- The distance is nonnegative. -/
theorem bkDist_nonneg (p q : ℤ × ℤ) : 0 ≤ bkDist p q := Real.sqrt_nonneg _

/-- The square of the distance is the squared distance. -/
theorem bkDist_sq (p q : ℤ × ℤ) : bkDist p q ^ 2 = bkDistSq p q := by
  unfold bkDist
  rw [Real.sq_sqrt (by exact_mod_cast bkDistSq_nonneg p q)]

/-- The distance is symmetric. -/
theorem bkDist_comm (p q : ℤ × ℤ) : bkDist p q = bkDist q p := by
  rw [bkDist, bkDist, bkDistSq_comm]

/-- The distance from a point to itself is zero. -/
@[simp]
theorem bkDist_self (p : ℤ × ℤ) : bkDist p p = 0 := by
  simp [bkDist]

/-- The distance between `p` and `q` vanishes iff `p = q`. -/
@[simp]
theorem bkDist_eq_zero_iff {p q : ℤ × ℤ} : bkDist p q = 0 ↔ p = q := by
  rw [bkDist, Real.sqrt_eq_zero (by exact_mod_cast bkDistSq_nonneg p q)]
  exact_mod_cast bkDistSq_eq_zero_iff

/-- The distance is the square root of the sum of the squared real coordinate differences. -/
theorem bkDist_eq (p q : ℤ × ℤ) :
    bkDist p q = √(((bkJ p - bkJ q : ℤ) : ℝ) ^ 2 + ((bkL p - bkL q : ℤ) : ℝ) ^ 2) := by
  simp [bkDist, bkDistSq]

/-- Two points differing by one in the first coordinate are at distance one. -/
theorem bkDist_add_one_fst (a b : ℤ) : bkDist (a + 1, b) (a, b) = 1 := by
  simp [bkDist, bkDistSq, bkJ, bkL]

/-- Two points differing by one in the second coordinate are at distance one. -/
theorem bkDist_add_one_snd (a b : ℤ) : bkDist (a, b + 1) (a, b) = 1 := by
  simp [bkDist, bkDistSq, bkJ, bkL]

end CollatzPosDens
