/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.NormNum

/-!
# A lower bound for `e^9`

This file proves the elementary numerical bound `e^9 > 8000`. Since every term of the
exponential series at a nonnegative argument is nonnegative, `e^x` dominates each partial sum
`∑_{j=0}^{n} x^j / j!` for `x ≥ 0`. Taking `x = 9` and `n = 20`, the partial sum is an explicit
rational number, approximately `8099.5`, which exceeds `8000`.

## Main results

* `CollatzPosDens.exp_nine_gt`: `8000 < Real.exp 9`.
-/

@[expose] public section

namespace CollatzPosDens

open Finset in
/-- `e^9 > 8000`, from the partial sum `∑_{j=0}^{20} 9^j / j!` of the exponential series. -/
@[collatz_pos_dens "lem_s02_exp9"]
theorem exp_nine_gt : (8000 : ℝ) < Real.exp 9 := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9) 21)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]
  norm_num

end CollatzPosDens
