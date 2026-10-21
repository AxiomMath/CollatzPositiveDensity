/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.Complex.Exponential

/-!
# The quadratic Taylor upper bound for `exp (-t)`

For every real `t ≥ 0`, `exp (-t) ≤ 1 - t + t² / 2`.

## Main results

* `CollatzPosDens.exp_neg_le_one_sub_add_sq_div_two`: the bound `exp (-t) ≤ 1 - t + t² / 2`
  for all real `t ≥ 0`.

## Implementation notes

Rather than integrating twice from `0`, the proof uses the lower bound `1 + t + t² / 2 ≤ exp t`
for `t ≥ 0` (`Real.quadratic_le_exp_of_nonneg`) together with the identity
`(1 - t + t² / 2) (1 + t + t² / 2) = 1 + t⁴ / 4 ≥ 1`; multiplying through
`exp (-t) · exp t = 1` gives the claim.
-/

@[expose] public section

namespace CollatzPosDens

/-- The quadratic Taylor upper bound for the decaying exponential: `exp (-t) ≤ 1 - t + t² / 2`
for every real `t ≥ 0`. -/
@[collatz_pos_dens "lem_ch_exp_quadratic"]
theorem exp_neg_le_one_sub_add_sq_div_two {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg ht
  have hm : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have he := Real.exp_pos (-t)
  have hp : 0 < 1 - t + t ^ 2 / 2 := by nlinarith [sq_nonneg (t - 1)]
  nlinarith [mul_le_mul_of_nonneg_left hq he.le, sq_nonneg (t ^ 2),
    mul_le_mul_of_nonneg_left hq hp.le]

end CollatzPosDens
