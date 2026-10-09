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
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkStrip
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkRowstartSpec

/-!
# The angle at the corner of the canonical triangle

Let `ξ` be a unit, `ε > 0` and `p` a black point with canonical triangle
`Δ(p) = (j_*, l_*, s)`. Then `|ϑ(j_*, l_*)| = ε e^{-s}`. Indeed the corner `(j_*, l_*)` is
black (by `eq_bkRowStart_iff` with `a = r = j_*`), so `j_* ≤ ⌊n/2⌋` and
`one_third_le_three_zpow_mul_abs_bkTheta` gives `ϑ(j_*, l_*) ≠ 0`; then
`s = log (ε / |ϑ(j_*, l_*)|)` unwinds to the claim.

## Main results

* `CollatzPosDens.bkBlack_bkCanonTriangle_corner`: the corner of `Δ(p)` is black.
* `CollatzPosDens.abs_bkTheta_bkCanonTriangle_corner`: `|ϑ(j_*, l_*)| = ε e^{-s}`.

## Implementation notes

The argument only uses `0 < ε`, so the statement is made under that hypothesis alone rather
than `0 < ε < 1/4`. Black points are points of `𝒫`, which is recorded by the hypothesis
`p ∈ bkPoints` (needed to form `Δ(p)`).
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}

/-- The corner `(j_*(p), l_*(p))` of the canonical triangle at a black point `p ∈ 𝒫` is
black. -/
theorem bkBlack_bkCanonTriangle_corner (hp : p ∈ bkPoints)
    (hb : BkBlack n ξ ε p) :
    BkBlack n ξ ε (bkCanonTriangle n ξ ε p hp).corner := by
  obtain ⟨_, hle, hall, _⟩ := (eq_bkRowStart_iff hp hb (bkRowStart n ξ ε p)).1 rfl
  exact hall _ le_rfl hle

/-- **Value at the corner.** Let `ξ` be a unit, `ε > 0` and `p ∈ 𝒫` black, with canonical
triangle `Δ(p) = (j_*, l_*, s)`. Then `|ϑ(j_*, l_*)| = ε e^{-s}`. -/
@[collatz_pos_dens "lem_bk_corner_value"]
theorem abs_bkTheta_bkCanonTriangle_corner (hξ : IsResidueUnit ξ) (hε : 0 < ε)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) :
    |bkTheta n ξ (bkCanonTriangle n ξ ε p hp).corner| =
      ε * Real.exp (-(bkCanonTriangle n ξ ε p hp).s) := by
  have hc := bkBlack_bkCanonTriangle_corner hp hb
  have hcp : (bkCanonTriangle n ξ ε p hp).corner ∈ bkPoints :=
    (bkCanonTriangle n ξ ε p hp).one_le_j
  have hstrip := one_third_le_three_zpow_mul_abs_bkTheta hξ hcp hc.bkJ_le
  have hθ : 0 < |bkTheta n ξ (bkCanonTriangle n ξ ε p hp).corner| := by
    refine (abs_nonneg _).lt_of_ne fun h => ?_
    rw [← h, mul_zero] at hstrip
    norm_num at hstrip
  rw [bkCanonTriangle_s, bkCanonSize_def, ← bkCanonTriangle_corner hp, Real.exp_neg,
    Real.exp_log (div_pos hε hθ)]
  field_simp

end CollatzPosDens
