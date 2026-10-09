/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkStrip
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkCornerValue
public import CollatzPosDens.BlackSet.BkRowstartSpec

/-!
# The exact edge of a canonical triangle

Let `ξ` be a unit, `ε > 0` and `p` a black point with canonical triangle
`Δ(p) = (j_*, l_*, s)`. Then `j_* + s / log 9 ≤ n / 2 + 1 - log (1/ε) / log 9`.

Write `A = |ϑ(j_*, l_*)| = ε e^{-s} > 0`, so that `s = log (1/A) - log (1/ε)`. The corner
`(j_*, l_*)` is black, so `j_* ≤ ⌊n/2⌋` and the strip bound `1/3 ≤ 3^{n+1-2j_*} A` gives
`log (1/A) ≤ (n + 2 - 2 j_*) log 3 = (n/2 + 1 - j_*) log 9`. Substituting `log (1/A)` concludes.

## Main results

* `CollatzPosDens.bkCanonTriangle_j_add_s_div_log_nine_le`:
  `j_* + s / log 9 ≤ n / 2 + 1 - log (1/ε) / log 9`.

## Implementation notes

The argument only uses `0 < ε`, and the statement is made under that hypothesis alone rather
than `0 < ε < 1/4`. Black points are points of `𝒫`, which is recorded by the hypothesis
`p ∈ bkPoints` (needed to form `Δ(p)`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.4.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}

/-- **Exact edge of a canonical triangle.** Let `ξ` be a unit, `ε > 0` and `p ∈ 𝒫` black, with
canonical triangle `Δ(p) = (j_*, l_*, s)`. Then
`j_* + s / log 9 ≤ n / 2 + 1 - log (1/ε) / log 9`. -/
@[collatz_pos_dens "lem_bk_canon_edge"]
theorem bkCanonTriangle_j_add_s_div_log_nine_le (hξ : IsResidueUnit ξ) (hε : 0 < ε)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) :
    ((bkCanonTriangle n ξ ε p hp).j : ℝ) + (bkCanonTriangle n ξ ε p hp).s / Real.log 9 ≤
      (n : ℝ) / 2 + 1 - Real.log (1 / ε) / Real.log 9 := by
  set T := bkCanonTriangle n ξ ε p hp
  have hc := bkBlack_bkCanonTriangle_corner hp hb
  have hcp : T.corner ∈ bkPoints := T.one_le_j
  have hstrip := one_third_le_three_zpow_mul_abs_bkTheta hξ hcp hc.bkJ_le
  have hA := abs_bkTheta_bkCanonTriangle_corner hξ hε hp hb
  rw [hA] at hstrip
  have hj : bkJ T.corner = T.j := rfl
  rw [hj] at hstrip
  have hApos : 0 < ε * Real.exp (-T.s) := by positivity
  have hpow : (0 : ℝ) < (3 : ℝ) ^ ((n : ℤ) + 1 - 2 * T.j) := by positivity
  have hlog := Real.log_le_log (by norm_num) hstrip
  rw [Real.log_mul hpow.ne' hApos.ne', Real.log_zpow, Real.log_mul hε.ne' (Real.exp_pos _).ne',
    Real.log_exp, one_div, Real.log_inv] at hlog
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h9 := log_nine_eq_two_mul_log_three
  have h9pos : 0 < Real.log 9 := by rw [h9]; positivity
  have key : T.s ≤ ((n : ℝ) / 2 + 1 - T.j) * Real.log 9 + Real.log ε := by
    rw [h9]; push_cast at hlog; nlinarith
  have key' : T.s / Real.log 9 ≤ (n : ℝ) / 2 + 1 - T.j + Real.log ε / Real.log 9 := by
    rw [div_le_iff₀ h9pos, add_mul, div_mul_cancel₀ _ h9pos.ne']
    exact key
  rw [one_div, Real.log_inv, neg_div]
  linarith

end CollatzPosDens
