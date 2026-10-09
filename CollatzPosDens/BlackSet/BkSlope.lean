/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr

/-!
# The slope `α = log 2 / log 9`

The real constant `α := log 2 / log 9 = log_9 2`, the slope of the black set in the
two-dimensional picture of the Collatz dynamics. It lies strictly between `0` and `1`
(in fact `α < 1 / 3`, since `2 ^ 3 < 9`).

## Main definitions

* `CollatzPosDens.alpha`: the constant `log 2 / log 9`.

## Main results

* `CollatzPosDens.alpha_eq_logb`: `α = log_9 2`.
* `CollatzPosDens.alpha_eq_div_two_mul_log_three`: `α = log 2 / (2 log 3)`.
* `CollatzPosDens.alpha_pos`, `CollatzPosDens.alpha_lt_one`: `0 < α < 1`.
* `CollatzPosDens.alpha_lt_one_div_three`: `α < 1 / 3`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The slope `α := log 2 / log 9`. -/
@[collatz_pos_dens "def_bk_slope"]
noncomputable def alpha : ℝ := Real.log 2 / Real.log 9

/-- `α` equals `log 2 / log 9`. -/
lemma alpha_def : alpha = Real.log 2 / Real.log 9 := rfl

/-- `α` is the base-`9` logarithm of `2`. -/
lemma alpha_eq_logb : alpha = Real.logb 9 2 := rfl

/-- `log 9 = 2 log 3`, since `9 = 3 ^ 2`. -/
lemma log_nine_eq_two_mul_log_three : Real.log 9 = 2 * Real.log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- `α log 9 = log 2`. -/
lemma alpha_mul_log_nine : alpha * Real.log 9 = Real.log 2 :=
  div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne'

/-- `α = log 2 / (2 log 3)`, since `9 = 3 ^ 2`. -/
lemma alpha_eq_div_two_mul_log_three : alpha = Real.log 2 / (2 * Real.log 3) := by
  rw [alpha_def, log_nine_eq_two_mul_log_three]

/-- `α` is positive. -/
lemma alpha_pos : 0 < alpha :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

/-- `α < 1 / 3`, since `2 ^ 3 < 9`. -/
lemma alpha_lt_one_div_three : alpha < 1 / 3 := by
  rw [alpha_def, div_lt_iff₀ (Real.log_pos (by norm_num))]
  have : Real.log (2 ^ 3) < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at this
  push_cast at this
  linarith

/-- `α < 1`. -/
lemma alpha_lt_one : alpha < 1 :=
  alpha_lt_one_div_three.trans (by norm_num)

end CollatzPosDens
