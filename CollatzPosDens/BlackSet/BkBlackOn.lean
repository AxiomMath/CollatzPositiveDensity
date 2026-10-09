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
public import CollatzPosDens.BlackSet.BkMemberLeft
public import CollatzPosDens.BlackSet.BkSeBound
public import CollatzPosDens.BlackSet.BkSeWeight
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkCanonEdge
public import CollatzPosDens.BlackSet.BkCornerValue
public import CollatzPosDens.BlackSet.BkInset

/-!
# The canonical triangle is black

Let `ξ` be a unit, `0 < ε < 1/27` and `p` a black point with canonical triangle
`Δ(p) = (j_*, l_*, s)`. Every point `q ∈ Δ(p)` is black.

Writing `c = (j_*, l_*)`, membership gives `j(c) ≤ j(q)`, `l(q) ≤ l(c)` and `se(c, q) ≤ s`, so
the south-east bound and the value at the corner give `|ϑ(q)| ≤ e^{s} · ε e^{-s} = ε`. The
left-edge bound, the exact edge of `Δ(p)` and the inset margin give
`j(q) ≤ j_* + s / log 9 ≤ n/2 + 1 - log(1/ε) / log 9 < n/2 - 1/2`, so `2 j(q) < n - 1` and
`j(q) ≤ ⌊n/2⌋`.

## Main results

* `CollatzPosDens.bkBlack_of_mem_bkCanonTriangle`: points of `Δ(p)` are black.

## Implementation notes

Black points are points of `𝒫`, which is recorded by the hypothesis `p ∈ bkPoints` (needed to
form `Δ(p)`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.4.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p q : ℤ × ℤ}

/-- **Canonical triangles are black.** Let `ξ` be a unit, `0 < ε < 1/27` and `p ∈ 𝒫` black.
Then every point `q ∈ Δ(p)` is black. -/
@[collatz_pos_dens "lem_bk_black_on"]
theorem bkBlack_of_mem_bkCanonTriangle (hξ : IsResidueUnit ξ) (hε : 0 < ε)
    (hε' : ε < 1 / 27) (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p)
    (hq : q ∈ bkCanonTriangle n ξ ε p hp) : BkBlack n ξ ε q := by
  set T := bkCanonTriangle n ξ ε p hp
  refine ⟨?_, ?_⟩
  · have hedge := bkCanonTriangle_j_add_s_div_log_nine_le hξ hε hp hb
    have hleft := BkTriangle.bkJ_le_of_mem hq
    have hinset := three_halves_lt_log_inv_div_log_nine hε hε'
    have h2 : 2 * bkJ q < (n : ℤ) - 1 := by
      have : ((2 * bkJ q : ℤ) : ℝ) < (((n : ℤ) - 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have : bkJ q ≤ (n : ℤ) / 2 := by omega
    exact_mod_cast this
  · have hse := abs_bkTheta_le_exp_bkSe_mul n ξ T.corner_mem_bkPoints
      (BkTriangle.mem_bkPoints_of_mem hq) (BkTriangle.j_le_of_mem hq)
      (BkTriangle.le_l_of_mem hq)
    rw [abs_bkTheta_bkCanonTriangle_corner hξ hε hp hb] at hse
    calc |bkTheta n ξ q| ≤ Real.exp (bkSe T.corner q) * (ε * Real.exp (-T.s)) := hse
      _ ≤ Real.exp T.s * (ε * Real.exp (-T.s)) := by
          gcongr
          exact BkTriangle.bkSe_corner_le_of_mem hq
      _ = ε := by rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end CollatzPosDens
