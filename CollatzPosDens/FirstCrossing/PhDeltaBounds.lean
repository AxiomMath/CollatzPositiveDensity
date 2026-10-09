/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhDelta

/-!
# Numerical bounds on the logarithmic growth rate `δ`

The logarithmic growth rate `δ = log₂ (101/100)` satisfies
$$\frac{1}{70} < \delta < \frac{1}{69}.$$
Since `x ↦ 2 ^ x` is strictly increasing, `δ > 1/70` is equivalent to `2 < (101/100)^70`, i.e.
`2 · 100^70 < 101^70`, and `δ < 1/69` is equivalent to `(101/100)^69 < 2`, i.e.
`101^69 < 2 · 100^69`; both are exact rational comparisons.

## Main results

* `CollatzPosDens.logGrowthRate_bounds`: `1/70 < δ ∧ δ < 1/69`.
* `CollatzPosDens.one_div_seventy_lt_logGrowthRate`: `1/70 < δ`.
* `CollatzPosDens.logGrowthRate_lt_one_div_sixtyNine`: `δ < 1/69`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The logarithmic growth rate satisfies `1/70 < δ`. -/
theorem one_div_seventy_lt_logGrowthRate : (1 : ℝ) / 70 < logGrowthRate := by
  rw [logGrowthRate_def, Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num), one_div]
  have h := Real.rpow_inv_natCast_pow (x := 2) (n := 70) (by norm_num) (by norm_num)
  push_cast at h
  exact lt_of_pow_lt_pow_left₀ 70 (by norm_num) (by rw [h]; norm_num)

/-- The logarithmic growth rate satisfies `δ < 1/69`. -/
theorem logGrowthRate_lt_one_div_sixtyNine : logGrowthRate < (1 : ℝ) / 69 := by
  rw [logGrowthRate_def, Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num), one_div]
  have h := Real.rpow_inv_natCast_pow (x := 2) (n := 69) (by norm_num) (by norm_num)
  push_cast at h
  exact lt_of_pow_lt_pow_left₀ 69 (by positivity) (by rw [h]; norm_num)

/-- The logarithmic growth rate satisfies `1/70 < δ < 1/69`. -/
@[collatz_pos_dens "lem_ph_delta_bounds"]
theorem logGrowthRate_bounds : (1 : ℝ) / 70 < logGrowthRate ∧ logGrowthRate < (1 : ℝ) / 69 :=
  ⟨one_div_seventy_lt_logGrowthRate, logGrowthRate_lt_one_div_sixtyNine⟩

end CollatzPosDens
