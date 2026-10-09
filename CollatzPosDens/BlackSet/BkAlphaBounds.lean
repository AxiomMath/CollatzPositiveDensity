/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope

/-!
# Numerical bounds on the slope `α = log 2 / log 9`

The slope `α = log 2 / log 9` satisfies `5 / 16 ≤ α ≤ 2 / 5`. The lower bound comes from
`9 ^ 5 = 59049 ≤ 65536 = 2 ^ 16`, the upper bound from `2 ^ 5 = 32 ≤ 81 = 9 ^ 2`.

## Main results

* `CollatzPosDens.five_div_sixteen_le_alpha`: `5 / 16 ≤ α`.
* `CollatzPosDens.alpha_le_two_div_five`: `α ≤ 2 / 5`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The slope `α = log 2 / log 9` satisfies `5 / 16 ≤ α`. -/
@[collatz_pos_dens "lem_bk_alpha_bounds"]
theorem five_div_sixteen_le_alpha : 5 / 16 ≤ alpha := by
  rw [alpha_def, le_div_iff₀ (Real.log_pos (by norm_num))]
  have h : Real.log ((9 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 16) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- The slope `α = log 2 / log 9` satisfies `α ≤ 2 / 5`. -/
@[collatz_pos_dens "lem_bk_alpha_bounds"]
theorem alpha_le_two_div_five : alpha ≤ 2 / 5 := by
  rw [alpha_def, div_le_iff₀ (Real.log_pos (by norm_num))]
  have h : Real.log ((2 : ℝ) ^ 5) ≤ Real.log ((9 : ℝ) ^ 2) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

end CollatzPosDens
