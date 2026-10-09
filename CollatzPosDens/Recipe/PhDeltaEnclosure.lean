/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhDelta
public import CollatzPosDens.Transfer.AtanhBounds

/-!
# A twenty-one-digit enclosure of `δ`

The logarithmic growth rate `δ = log₂ (101/100) = log (101/100) / log 2` satisfies
$$0.014355292977070041430 < \delta < 0.014355292977070041432.$$

The inverse hyperbolic tangent enclosure of the logarithm, at `y = 2` (`t = 1/3`) and at
`y = 101/100` (`t = 1/201`), gives rational enclosures of `log 2` and `log (101/100)`; rounded
outward to `24` decimal places they read
`0.693147180559945309417230 < log 2 < 0.693147180559945309417233` and
`0.009950330853168082848215 < log (101/100) < 0.009950330853168082848216`.
Dividing the lower (upper) bound of the numerator by the upper (lower) bound of the denominator
and comparing exactly with the stated decimals proves the claim.

## Main results

* `CollatzPosDens.logGrowthRate_mem_Ioo`: the enclosure of `δ`.
* `CollatzPosDens.logGrowthRate_log_two_mem_Ioo`,
  `CollatzPosDens.logGrowthRate_log_growthRatio_mem_Ioo`: the enclosures of `log 2` and
  `log (101/100)` used for it.

## Implementation notes

The partial sums use `n = 23` terms of the series at `t = 1/3` and `n = 5` terms at
`t = 1/201`, with the bounds rounded to `24` decimal places; these suffice for the stated
precision.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- `0.693147180559945309417230 < log 2 < 0.693147180559945309417233`. -/
theorem logGrowthRate_log_two_mem_Ioo :
    Real.log 2 ∈ Set.Ioo (693147180559945309417230 / 10 ^ 24 : ℝ)
      (693147180559945309417233 / 10 ^ 24) := by
  obtain ⟨h1, h2⟩ := log_mem_atanh_partialSum (y := 2) (by norm_num) 23
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

/-- `0.009950330853168082848215 < log (101/100) < 0.009950330853168082848216`. -/
theorem logGrowthRate_log_growthRatio_mem_Ioo :
    Real.log (101 / 100) ∈ Set.Ioo (9950330853168082848215 / 10 ^ 24 : ℝ)
      (9950330853168082848216 / 10 ^ 24) := by
  obtain ⟨h1, h2⟩ := log_mem_atanh_partialSum (y := 101 / 100) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

/-- **Enclosure of `δ`.** `0.014355292977070041430 < δ < 0.014355292977070041432`. -/
@[collatz_pos_dens "lem_ph_delta_enclosure"]
theorem logGrowthRate_mem_Ioo :
    logGrowthRate ∈ Set.Ioo (14355292977070041430 / 10 ^ 21 : ℝ)
      (14355292977070041432 / 10 ^ 21) := by
  obtain ⟨a1, a2⟩ := logGrowthRate_log_two_mem_Ioo
  obtain ⟨b1, b2⟩ := logGrowthRate_log_growthRatio_mem_Ioo
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  rw [logGrowthRate_def, Real.logb]
  exact ⟨(lt_div_iff₀ hpos).2 (by linarith), (div_lt_iff₀ hpos).2 (by linarith)⟩

end CollatzPosDens
