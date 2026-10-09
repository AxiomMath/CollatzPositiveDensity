/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.Complex.Exponential

/-!
# A quadratic upper bound for `exp (-x)` on the nonnegative reals

For every real `x ≥ 0` we have `exp (-x) ≤ 1 - x + x ^ 2 / 2`: the second Taylor polynomial of
`exp (-x)` at `0` bounds it from above on `[0, ∞)`.

## Main results

* `CollatzPosDens.exp_neg_le_one_sub_add_sq_div_two`:
  `exp (-x) ≤ 1 - x + x ^ 2 / 2` for `0 ≤ x`.

## Implementation notes

Rather than arguing by convexity of `1 - x + x ^ 2 / 2 - exp (-x)`, we use the lower bound
`1 + x + x ^ 2 / 2 ≤ exp x` for `x ≥ 0` together with the identity
`(1 - x + x ^ 2 / 2) (1 + x + x ^ 2 / 2) = 1 + x ^ 4 / 4 ≥ 1`, so that
`exp (-x) = (exp x)⁻¹ ≤ (1 + x + x ^ 2 / 2)⁻¹ ≤ 1 - x + x ^ 2 / 2`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every real `x ≥ 0`, `exp (-x) ≤ 1 - x + x ^ 2 / 2`. -/
@[collatz_pos_dens "lem_mo_discount"]
theorem exp_neg_le_one_sub_add_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  have h1 : Real.exp (-x) ≤ (1 + x + x ^ 2 / 2)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hpos (Real.quadratic_le_exp_of_nonneg hx)
  refine h1.trans ?_
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith [pow_nonneg hx 4]

end CollatzPosDens
