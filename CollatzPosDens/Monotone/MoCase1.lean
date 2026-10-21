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
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Chi
public import CollatzPosDens.Transfer.S02Z
public import CollatzPosDens.Monotone.MoHoldAverage
public import CollatzPosDens.Monotone.MoInvpowMoment

/-!
# Case 1 of the monotonicity step: a white boundary point

Fix a Fourier index `ι`, a level `n`, a residue `ξ ∈ G_n` and a colour threshold `ε`, write
`J = ⌊n/2⌋`, and form the weighted suprema `Q_m` with the exponent `A_*(ι)`. If `m ≥ 2^40` and
`p ∈ 𝒫` is white with `j(p) + m = J`, then `Q(p) ≤ e^{-z_* + χ_*/2} m^{-A_*(ι)} Q_{m-1}`.

By `chQ_le_mul_tsum` and `chWhiteFactor_of_isBkWhite`, `Q(p) ≤ e^{-z_*} ∑_h η(h) Q(p + h)`. By
`tsum_holdLaw_mul_chQ_add_le` the sum is at most `(∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A}) Q_{m-1}`
with `A = A_*(ι)`, since `A ≥ 0` (it is `21193/10000` or `17/10`). As `0 < χ_* = 63/2500 ≤ 1/32`,
the quantity `(256 A/χ_*)^2 + 2` is `1839690755842/3969` or `1183744007938/3969`, below
`2^30 ≤ 2^40 ≤ m`, so `tsum_nu45_mul_max_rpow_neg_le` bounds the bracket by `m^{-A} e^{χ_*/2}`. As
`Q_{m-1} ≥ 0`, the bound follows.

## Main results

* `CollatzPosDens.chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite`: the white-case bound.

## Implementation notes

The colour threshold is fixed to `ε_*` in the paper; the argument does not use its value, and the
statement is given for every real `ε`. The integer `m ≥ 2^40` is taken to be a natural number, so
that `Q_{m-1}` is the supremum at the natural number `m - 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Case 1: a white boundary point.** Let `ι` be a Fourier index, `m ≥ 2^40`, and let
`p ∈ 𝒫` be white with `j(p) + m = ⌊n/2⌋`. Then `Q(p) ≤ e^{-z_* + χ_*/2} m^{-A_*(ι)} Q_{m-1}`,
with `Q_{m-1}` formed with the exponent `A_*(ι)`. -/
@[collatz_pos_dens "lem_mo_case1"]
theorem chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    {m : ℕ} (hm : 2 ^ 40 ≤ m) {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (hwhite : IsBkWhite n ξ ε p) (hpm : bkJ p + m = ((n / 2 : ℕ) : ℤ)) :
    chQ n ξ ε p ≤
      exp (-(zStar : ℝ) + (chiStar : ℝ) / 2) * (m : ℝ) ^ (-(Aexp ι : ℝ)) *
        chQm n ξ ε (Aexp ι : ℝ) (m - 1) := by
  have hA : (0 : ℝ) ≤ (Aexp ι : ℝ) := by exact_mod_cast (Aexp_pos ι).le
  have hχ₀ : (0 : ℝ) < (chiStar : ℝ) := by rw [chiStar_cast]; norm_num
  have hχ₁ : (chiStar : ℝ) ≤ 1 / 32 := by rw [chiStar_cast]; norm_num
  have hm' : (256 * (Aexp ι : ℝ) / (chiStar : ℝ)) ^ 2 + 2 ≤ ((m : ℤ) : ℝ) := by
    have hmR : (2 : ℝ) ^ 40 ≤ m := by exact_mod_cast hm
    have h30 : (256 * (Aexp ι : ℝ) / (chiStar : ℝ)) ^ 2 + 2 < 2 ^ 30 := by
      rw [chiStar_cast]
      cases ι
      · rw [Aexp_cast_o]; norm_num
      · rw [Aexp_cast_b]; norm_num
    rw [Int.cast_natCast]
    linarith [show (2 : ℝ) ^ 30 ≤ 2 ^ 40 by norm_num]
  have hmom := tsum_nu45_mul_max_rpow_neg_le hA hχ₀ hχ₁ hm'
  have hrec := chQ_le_mul_tsum n ξ ε hp
  rw [chWhiteFactor_of_isBkWhite hwhite] at hrec
  rw [Int.cast_natCast] at hmom
  calc chQ n ξ ε p
      ≤ exp (-(zStar : ℝ)) * ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) :=
        hrec
    _ ≤ exp (-(zStar : ℝ)) *
          ((m : ℝ) ^ (-(Aexp ι : ℝ)) * exp ((chiStar : ℝ) / 2) *
            chQm n ξ ε (Aexp ι : ℝ) (m - 1)) := by
        gcongr
        exact (tsum_holdLaw_mul_chQ_add_le n ξ ε hA m hp hpm).trans
          (mul_le_mul_of_nonneg_right hmom (chQm_nonneg n ξ ε _ (m - 1)))
    _ = exp (-(zStar : ℝ) + (chiStar : ℝ) / 2) * (m : ℝ) ^ (-(Aexp ι : ℝ)) *
          chQm n ξ ε (Aexp ι : ℝ) (m - 1) := by
        rw [exp_add]; ring

end CollatzPosDens
