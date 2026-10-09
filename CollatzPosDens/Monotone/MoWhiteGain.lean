/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.W
public import CollatzPosDens.Transfer.Z
public import CollatzPosDens.Monotone.MoDiscount

/-!
# The white gain inequality `exp (-z_* + w_*/2) ≤ 1 - 3 z_* / 5`

With the white Fourier penalty `z_* = 21/500` and the near-top tilt allowance `w_* = 63/2500`,
the exponential factor `exp (-z_* + w_*/2)` is at most `1 - (3/5) z_*`.

The proof sets `v = z_* - w_*/2 = 147/5000 ≥ 0` and applies the quadratic bound
`exp (-v) ≤ 1 - v + v ^ 2 / 2 = 48551609/50000000`, which is below
`1 - (3/5) z_* = 48740000/50000000`.

## Main results

* `CollatzPosDens.exp_neg_zStar_add_wStar_div_two_le`:
  `exp (-z_* + w_*/2) ≤ 1 - (3/5) z_*`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The white gain inequality: `exp (-z_* + w_*/2) ≤ 1 - (3/5) z_*`. -/
@[collatz_pos_dens "lem_mo_white_gain"]
theorem exp_neg_zStar_add_wStar_div_two_le :
    Real.exp (-(zStar : ℝ) + (wStar : ℝ) / 2) ≤ 1 - 3 / 5 * (zStar : ℝ) := by
  have h := exp_neg_le_one_sub_add_sq_div_two (x := (zStar : ℝ) - (wStar : ℝ) / 2)
    (by rw [zStar_cast, wStar_cast]; norm_num)
  rw [show -(zStar : ℝ) + (wStar : ℝ) / 2 = -((zStar : ℝ) - (wStar : ℝ) / 2) by ring]
  refine h.trans ?_
  rw [zStar_cast, wStar_cast]
  norm_num

end CollatzPosDens
