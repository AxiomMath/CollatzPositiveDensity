/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import CollatzPosDens.Attr

/-!
# A numerical bound on `(24/25)^{1169} (576/575)^{13725}`

This file proves the explicit inequality `(24/25)^{1169} (576/575)^{13725} < 1/3000000000`.

By `1 + s ≤ e^s` with `s = -1/25` and `s = 1/575`, the product is at most
`e^{-1169/25 + 13725/575} = e^{-13162/575} ≤ e^{-22}`, and the partial sum
`∑_{j=0}^{60} 22^j / j! ≈ 3.5849 · 10^9` of the exponential series bounds `e^{22}` from below
by more than `3 · 10^9`.

## Main results

* `CollatzPosDens.exp_twentyTwo_gt`: `3000000000 < e^{22}`.
* `CollatzPosDens.fcFirstEarly_value_lt`: `(24/25)^{1169} (576/575)^{13725} < 1/3000000000`.

## Implementation notes

The powers `(24/25)^{1169}` and `(576/575)^{13725}` are never evaluated: they are compared with
exponentials through `pow_le_pow_left₀` while the exponents stay symbolic.
-/

@[expose] public section

namespace CollatzPosDens

open Finset Real

/-- `e^{22} > 3000000000`, from the partial sum `∑_{j=0}^{60} 22^j / j!` of the exponential
series. -/
theorem exp_twentyTwo_gt : (3000000000 : ℝ) < exp 22 := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 22) 61)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]
  norm_num

/-- `(24/25)^{1169} (576/575)^{13725} < 1/3000000000`. -/
@[collatz_pos_dens "lem_fc_first_early_value"]
theorem fcFirstEarly_value_lt :
    (24 / 25 : ℝ) ^ 1169 * (576 / 575) ^ 13725 < 1 / 3000000000 := by
  have h1 : (24 / 25 : ℝ) ^ 1169 ≤ exp (-1 / 25) ^ 1169 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (-1 / 25 : ℝ)]) _
  have h2 : (576 / 575 : ℝ) ^ 13725 ≤ exp (1 / 575) ^ 13725 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (1 / 575 : ℝ)]) _
  have h3 : exp (-1 / 25) ^ 1169 * exp (1 / 575) ^ 13725 ≤ exp (-22) := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
    exact exp_le_exp.2 (by norm_num)
  have h4 : exp (-22) < 1 / 3000000000 := by
    rw [exp_neg, one_div]
    exact inv_strictAnti₀ (by norm_num) exp_twentyTwo_gt
  calc (24 / 25 : ℝ) ^ 1169 * (576 / 575) ^ 13725
      ≤ exp (-1 / 25) ^ 1169 * exp (1 / 575) ^ 13725 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ < 1 / 3000000000 := h3.trans_lt h4

end CollatzPosDens
