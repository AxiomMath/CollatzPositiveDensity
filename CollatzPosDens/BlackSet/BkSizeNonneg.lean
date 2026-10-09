/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkCornerValue
public import CollatzPosDens.BlackSet.BkRowstartSpec

/-!
# Canonical sizes are nonnegative

Let `ξ` be a unit, `0 < ε` and `p ∈ bkPoints` a black point (`BkBlack`) with canonical
triangle `Δ(p) = bkCanonTriangle n ξ ε p = (j_*, l_*, s)`. Then `s ≥ 0`. Indeed the corner
`(j_*, l_*)` is black (`bkBlack_bkCanonTriangle_corner`), so `|ϑ(j_*, l_*)| ≤ ε`, while
`|ϑ(j_*, l_*)| = ε e^{-s}` (`abs_bkTheta_bkCanonTriangle_corner`); hence `ε e^{-s} ≤ ε`, that is
`e^{-s} ≤ 1`, so `s ≥ 0`.

## Main results

* `CollatzPosDens.bkCanonTriangle_s_nonneg`: the size of `Δ(p)` is nonnegative.

## Implementation notes

The statement assumes only `0 < ε`, rather than `0 < ε < 1/4`. The hypothesis `p ∈ bkPoints`
is needed to form `Δ(p)`.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}

/-- **Canonical sizes are nonnegative.** Let `ξ` be a unit, `ε > 0` and `p ∈ 𝒫` black, with
canonical triangle `Δ(p) = (j_*, l_*, s)`. Then `s ≥ 0`. -/
@[collatz_pos_dens "lem_bk_size_nonneg"]
theorem bkCanonTriangle_s_nonneg (hξ : IsResidueUnit ξ) (hε : 0 < ε)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) :
    0 ≤ (bkCanonTriangle n ξ ε p hp).s := by
  have hle := (bkBlack_bkCanonTriangle_corner hp hb).abs_bkTheta_le
  rw [abs_bkTheta_bkCanonTriangle_corner hξ hε hp hb] at hle
  have h1 : Real.exp (-(bkCanonTriangle n ξ ε p hp).s) ≤ 1 := by
    by_contra h
    nlinarith [not_le.1 h]
  have := Real.exp_le_one_iff.1 h1
  linarith

end CollatzPosDens
