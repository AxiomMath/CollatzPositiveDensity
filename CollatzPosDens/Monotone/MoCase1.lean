/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChQRecursionLe
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.D1
public import CollatzPosDens.Transfer.W
public import CollatzPosDens.Transfer.Z
public import CollatzPosDens.Monotone.MoHoldAverage
public import CollatzPosDens.Monotone.MoInvpowMoment

/-!
# Case 1 of the monotonicity step: a white boundary point

Fix a level `n`, a residue `ξ ∈ G_n` and a colour threshold `ε`, write `J = ⌊n/2⌋`, and form
the weighted suprema `Q_m` with the exponent `A_*`. If `m ≥ D₁` and `p ∈ 𝒫` is white with
`j(p) + m = J`, then
`Q(p) ≤ e^{-z_* + w_*/2} m^{-A_*} Q_{m-1}`.

By the renewal inequality and whiteness, `Q(p) ≤ e^{-z_*} ∑_h η(h) Q(p + h)`. The one-hold
average bounds the sum by `(∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A_*}) Q_{m-1}`, and since
`D₁ = (256 A_*/w_*)^2 + 2` with `0 < w_* ≤ 1/32`, the bracket is at most `m^{-A_*} e^{w_*/2}`.
As `Q_{m-1} ≥ 0`, the bound follows.

## Main results

* `CollatzPosDens.chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite`: the white-case bound.

## Implementation notes

The argument does not use the value of the colour threshold, so the statement is given for every
real `ε` rather than only for `ε_*`. The integer `m ≥ D₁ > 2` is taken to be a natural number, so
that `Q_{m-1}` is the supremum at the natural number `m - 1`.

## References

* [Mazur, *Collatz positive density*], §8.3.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Case 1: a white boundary point.** Let `m ≥ D₁` and let `p ∈ 𝒫` be white with
`j(p) + m = ⌊n/2⌋`. Then `Q(p) ≤ e^{-z_* + w_*/2} m^{-A_*} Q_{m-1}`. -/
@[collatz_pos_dens "lem_mo_case1"]
theorem chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    {m : ℕ} (hm : (D1 : ℝ) ≤ m) {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (hwhite : IsBkWhite n ξ ε p) (hpm : bkJ p + m = ((n / 2 : ℕ) : ℤ)) :
    chQ n ξ ε p ≤
      exp (-(zStar : ℝ) + (wStar : ℝ) / 2) * (m : ℝ) ^ (-(Aexp : ℝ)) *
        chQm n ξ ε (Aexp : ℝ) (m - 1) := by
  have hA : (0 : ℝ) ≤ (Aexp : ℝ) := by norm_num [Aexp_cast]
  have hm' : (256 * (Aexp : ℝ) / (wStar : ℝ)) ^ 2 + 2 ≤ ((m : ℤ) : ℝ) := by
    have : (D1 : ℝ) = (256 * (Aexp : ℝ) / (wStar : ℝ)) ^ 2 + 2 := by
      rw [D1_def]
      push_cast
      ring
    rwa [Int.cast_natCast, ← this]
  have hmom :=
    tsum_nu45_mul_max_rpow_neg_le hA (by norm_num [wStar_cast]) (by norm_num [wStar_cast]) hm'
  have hrec := chQ_le_mul_tsum n ξ ε hp
  rw [chWhiteFactor_of_isBkWhite hwhite] at hrec
  rw [Int.cast_natCast] at hmom
  calc chQ n ξ ε p
      ≤ exp (-(zStar : ℝ)) * ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) :=
        hrec
    _ ≤ exp (-(zStar : ℝ)) *
          ((m : ℝ) ^ (-(Aexp : ℝ)) * exp ((wStar : ℝ) / 2) * chQm n ξ ε (Aexp : ℝ) (m - 1)) := by
        gcongr
        exact (tsum_holdLaw_mul_chQ_add_le n ξ ε hA m hp hpm).trans
          (mul_le_mul_of_nonneg_right hmom (chQm_nonneg n ξ ε _ (m - 1)))
    _ = exp (-(zStar : ℝ) + (wStar : ℝ) / 2) * (m : ℝ) ^ (-(Aexp : ℝ)) *
          chQm n ξ ε (Aexp : ℝ) (m - 1) := by
        rw [exp_add]
        ring

end CollatzPosDens
