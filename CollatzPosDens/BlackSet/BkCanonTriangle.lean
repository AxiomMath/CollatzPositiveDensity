/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.BlackSet.BkRowStart
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkTriangle

/-!
# The canonical triangle at a black point

Fix `n`, `ξ`, `ε`. For a black point `p` let `j_*(p)` and `l_*(p)` be the start of its row run
and the top of its column run. The *canonical triangle* at `p` is
`Δ(p) := (j_*(p), l_*(p), log (ε / |ϑ(j_*(p), l_*(p))|))`, with third entry `0` if
`ϑ(j_*(p), l_*(p)) = 0`.

## Main definitions

* `CollatzPosDens.bkCanonSize n ξ ε p`: the size `log (ε / |ϑ(j_*(p), l_*(p))|)`.
* `CollatzPosDens.bkCanonTriangle n ξ ε p hp`: the triangle `Δ(p)`.

## Main results

* `CollatzPosDens.one_le_bkRowStart`: `1 ≤ j_*(p)` for `p ∈ 𝒫`.
* `CollatzPosDens.bkCanonSize_eq_zero_of_bkTheta_eq_zero`: the size is `0` when the angle at the
  corner vanishes; `CollatzPosDens.bkCanonSize_eq_ite` states the size as a case split.
* `CollatzPosDens.bkCanonTriangle_j`, `bkCanonTriangle_l`, `bkCanonTriangle_s`,
  `bkCanonTriangle_corner`: the entries and corner of `Δ(p)`.

## Implementation notes

The triangle is defined for every `p ∈ 𝒫`, not only for black points; the hypothesis `p ∈ 𝒫` is
what makes `1 ≤ j_*(p)`, as a triangle requires. The convention "third entry `0` if
`ϑ = 0`" needs no case split: with Lean's conventions `ε / 0 = 0` and `Real.log 0 = 0`, so the
formula `Real.log (ε / |ϑ|)` already takes the value `0` there
(`bkCanonSize_eq_zero_of_bkTheta_eq_zero`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.4.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}

/-- For `p ∈ 𝒫`, the row start satisfies `1 ≤ j_*(p)`. -/
theorem one_le_bkRowStart (hp : p ∈ bkPoints) : 1 ≤ bkRowStart n ξ ε p := by
  by_cases h : ∃ a : ℤ, 1 ≤ a ∧ a ≤ bkJ p ∧
      ∀ r : ℤ, a ≤ r → r ≤ bkJ p → BkBlack n ξ ε (r, bkColTop n ξ ε p)
  · exact (bkRowStart_spec_of_exists h).1
  · rw [bkRowStart_eq_bkJ_of_not_exists h]
    exact mem_bkPoints.1 hp

/-- The size `log (ε / |ϑ(j_*(p), l_*(p))|)` of the canonical triangle at `p`; it is `0` when
`ϑ(j_*(p), l_*(p)) = 0`. -/
@[collatz_pos_dens "def_bk_canon_triangle"]
noncomputable def bkCanonSize (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : ℝ :=
  Real.log (ε / |bkTheta n ξ (bkRowStart n ξ ε p, bkColTop n ξ ε p)|)

/-- Unfolding lemma for `bkCanonSize`. -/
theorem bkCanonSize_def (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    bkCanonSize n ξ ε p =
      Real.log (ε / |bkTheta n ξ (bkRowStart n ξ ε p, bkColTop n ξ ε p)|) := rfl

/-- The size of the canonical triangle is `0` when the angle at its corner vanishes. -/
theorem bkCanonSize_eq_zero_of_bkTheta_eq_zero
    (h : bkTheta n ξ (bkRowStart n ξ ε p, bkColTop n ξ ε p) = 0) :
    bkCanonSize n ξ ε p = 0 := by
  rw [bkCanonSize_def, h, abs_zero, div_zero, Real.log_zero]

/-- The size of the canonical triangle as a case split on whether the angle at its corner
vanishes. -/
theorem bkCanonSize_eq_ite (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    bkCanonSize n ξ ε p =
      if bkTheta n ξ (bkRowStart n ξ ε p, bkColTop n ξ ε p) = 0 then 0
      else Real.log (ε / |bkTheta n ξ (bkRowStart n ξ ε p, bkColTop n ξ ε p)|) := by
  split_ifs with h
  · exact bkCanonSize_eq_zero_of_bkTheta_eq_zero h
  · rfl

/-- The canonical triangle `Δ(p) := (j_*(p), l_*(p), log (ε / |ϑ(j_*(p), l_*(p))|))` at a point
`p ∈ 𝒫`, with third entry `0` if `ϑ(j_*(p), l_*(p)) = 0`. -/
@[collatz_pos_dens "def_bk_canon_triangle"]
noncomputable def bkCanonTriangle (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ)
    (hp : p ∈ bkPoints) : BkTriangle where
  j := bkRowStart n ξ ε p
  l := bkColTop n ξ ε p
  s := bkCanonSize n ξ ε p
  one_le_j := one_le_bkRowStart hp

/-- The first entry of `Δ(p)` is the row start `j_*(p)`. -/
@[simp]
theorem bkCanonTriangle_j (hp : p ∈ bkPoints) :
    (bkCanonTriangle n ξ ε p hp).j = bkRowStart n ξ ε p := rfl

/-- The second entry of `Δ(p)` is the column top `l_*(p)`. -/
@[simp]
theorem bkCanonTriangle_l (hp : p ∈ bkPoints) :
    (bkCanonTriangle n ξ ε p hp).l = bkColTop n ξ ε p := rfl

/-- The size of `Δ(p)` is `log (ε / |ϑ(j_*(p), l_*(p))|)`. -/
@[simp]
theorem bkCanonTriangle_s (hp : p ∈ bkPoints) :
    (bkCanonTriangle n ξ ε p hp).s = bkCanonSize n ξ ε p := rfl

/-- The corner of `Δ(p)` is `(j_*(p), l_*(p))`. -/
@[simp]
theorem bkCanonTriangle_corner (hp : p ∈ bkPoints) :
    (bkCanonTriangle n ξ ε p hp).corner = (bkRowStart n ξ ε p, bkColTop n ξ ε p) := rfl

end CollatzPosDens
