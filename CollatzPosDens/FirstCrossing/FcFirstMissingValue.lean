/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.NormNum

/-!
# An explicit upper bound for `(31/32)^{1170} (1024/1023)^{19362}`

This file proves the numerical inequality `(31/32)^{1170} (1024/1023)^{19362} < 1/39000000`.

From `1 + s ≤ e^s` with `s = -1/32` and `s = 1/1023`, the product is at most
`e^{-1170/32 + 19362/1023}`, and `1170/32 - 19362/1023 = 96221/5456 ≥ 35/2`. Since `e^x`
dominates each partial sum of its series for `x ≥ 0`, `e^{35/2} ≥ ∑_{j=0}^{50} (35/2)^j / j!`, an
explicit rational number (about `3.98 · 10^7`) exceeding `39000000`.

## Main results

* `CollatzPosDens.fcFirstMissingValue_lt`: `(31/32)^{1170} (1024/1023)^{19362} < 1/39000000`.

## Implementation notes

The two large powers are never evaluated: each is compared with a power of an exponential and
the exponents are combined.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Real

namespace CollatzPosDens

open Finset in
/-- `e^{35/2} > 39000000`, from the partial sum `∑_{j=0}^{50} (35/2)^j / j!` of the exponential
series. -/
private theorem fcFirstMissingValue_exp_gt : (39000000 : ℝ) < exp (35 / 2) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 35 / 2) 51)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]
  norm_num

/-- `(31/32)^{1170} (1024/1023)^{19362} < 1/39000000`. -/
@[collatz_pos_dens "lem_fc_first_missing_value"]
theorem fcFirstMissingValue_lt :
    (31 / 32 : ℝ) ^ 1170 * (1024 / 1023 : ℝ) ^ 19362 < 1 / 39000000 := by
  have h1 : (31 / 32 : ℝ) ^ 1170 ≤ exp (-1 / 32) ^ 1170 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (-1 / 32 : ℝ)]) _
  have h2 : (1024 / 1023 : ℝ) ^ 19362 ≤ exp (1 / 1023) ^ 19362 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (1 / 1023 : ℝ)]) _
  have h3 : exp (-1 / 32) ^ 1170 * exp (1 / 1023) ^ 19362 ≤ exp (-(35 / 2)) := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add, exp_le_exp]
    norm_num
  have h4 : exp (-(35 / 2)) < 1 / 39000000 := by
    rw [exp_neg, one_div]
    exact inv_strictAnti₀ (by norm_num) fcFirstMissingValue_exp_gt
  calc (31 / 32 : ℝ) ^ 1170 * (1024 / 1023 : ℝ) ^ 19362
      ≤ exp (-1 / 32) ^ 1170 * exp (1 / 1023) ^ 19362 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ < 1 / 39000000 := h3.trans_lt h4

end CollatzPosDens
