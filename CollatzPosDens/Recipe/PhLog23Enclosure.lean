/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.AtanhBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A twenty-five digit enclosure of `log₂ 3`

The inverse hyperbolic tangent enclosure of the logarithm, taken at `y = 3` (so `t = 1/2`) with
`40` terms and at `y = 2` (so `t = 1/3`) with `26` terms, gives explicit rational numbers
`L₃ ≤ log 3 ≤ U₃` and `L₂ ≤ log 2 ≤ U₂`. Since `log₂ 3 = log 3 / log 2` and `log 2 > 0`, the two
exact rational inequalities `a · U₂ < L₃` and `U₃ < b · L₂` give `a < log₂ 3 < b` for the decimal
rationals `a = 1.5849625007211561814537388` and `b = 1.5849625007211561814537390`.

## Main results

* `CollatzPosDens.logb_two_three_mem_Ioo`:
  `1.5849625007211561814537388 < logb 2 3 < 1.5849625007211561814537390`.

## Implementation notes

Rather than taking `64` terms at both points and rounding the enclosures of `log 3` and `log 2`
outward to `30` decimals before dividing, `40` and `26` terms are used, and the partial sums are
compared with the decimal endpoints directly, without intermediate rounding; the comparisons are
exact rational arithmetic carried out by `norm_num`.
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- **Enclosure of `log₂ 3`.**
`1.5849625007211561814537388 < log₂ 3 < 1.5849625007211561814537390`. -/
@[collatz_pos_dens "lem_ph_log23_enclosure"]
theorem logb_two_three_mem_Ioo :
    (15849625007211561814537388 : ℝ) / 10 ^ 25 < logb 2 3 ∧
      logb 2 3 < (15849625007211561814537390 : ℝ) / 10 ^ 25 := by
  obtain ⟨hl3, hu3⟩ := log_mem_atanh_partialSum (y := 3) (by norm_num) 40
  obtain ⟨hl2, hu2⟩ := log_mem_atanh_partialSum (y := 2) (by norm_num) 26
  simp only [sum_range_succ, sum_range_zero] at hl3 hu3 hl2 hu2
  norm_num at hl3 hu3 hl2 hu2
  have h2 : 0 < log 2 := log_pos (by norm_num)
  rw [logb, lt_div_iff₀ h2, div_lt_iff₀ h2]
  constructor <;> nlinarith

end CollatzPosDens
