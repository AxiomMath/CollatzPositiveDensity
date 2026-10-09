/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The histogram growth factor `𝖦`

The histogram growth factor of the arithmetic recipe is the positive real number
$$\mathsf G = \mathsf g^{1/2} = (101/100)^{1/2},$$
the square root of the physical growth ratio `𝗀 = 101/100`. It satisfies `𝖦 ^ 2 = 𝗀`, hence
`𝖦 ^ (2 j) = 𝗀 ^ j` and `𝗀 ^ (j/2) = 𝖦 ^ j`, and the numerical bound `202/201 < 𝖦`, i.e.
`1/201 < 𝖦 - 1`.

## Main definitions

* `CollatzPosDens.histogramGrowth`: the real number `𝖦 = 𝗀 ^ (1/2)`.

## Main results

* `CollatzPosDens.histogramGrowth_eq_sqrt`: `𝖦 = √𝗀`.
* `CollatzPosDens.histogramGrowth_sq`: `𝖦 ^ 2 = 𝗀`.
* `CollatzPosDens.histogramGrowth_pos`, `CollatzPosDens.one_lt_histogramGrowth`:
  `0 < 𝖦` and `1 < 𝖦`.
* `CollatzPosDens.histogramGrowth_pow_eq_rpow`: `𝖦 ^ j = 𝗀 ^ (j/2)`.
* `CollatzPosDens.lt_histogramGrowth`: `202/201 < 𝖦`.

## Implementation notes

The ratio `𝗀` is rational; `𝖦` is defined as the real power `(𝗀 : ℝ) ^ (1/2 : ℝ)` of its cast,
so that powers with real exponents are positive real powers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The histogram growth factor `𝖦 = 𝗀 ^ (1/2) = (101/100) ^ (1/2) ∈ ℝ_{>0}`. -/
@[collatz_pos_dens "def_s04_growth"]
noncomputable def histogramGrowth : ℝ := (growthRatio : ℝ) ^ (1 / 2 : ℝ)

/-- `𝖦` is the real power `𝗀 ^ (1/2)`. -/
theorem histogramGrowth_def : histogramGrowth = (growthRatio : ℝ) ^ (1 / 2 : ℝ) := rfl

/-- `𝖦 = √𝗀`. -/
theorem histogramGrowth_eq_sqrt : histogramGrowth = Real.sqrt (growthRatio : ℝ) := by
  rw [histogramGrowth_def, Real.sqrt_eq_rpow]

/-- `𝖦 = √(101/100)`. -/
theorem histogramGrowth_eq_sqrt_num : histogramGrowth = Real.sqrt (101 / 100) := by
  rw [histogramGrowth_eq_sqrt, growthRatio_cast]

/-- `𝖦` is positive. -/
theorem histogramGrowth_pos : 0 < histogramGrowth := by
  rw [histogramGrowth_eq_sqrt]; exact Real.sqrt_pos.2 growthRatio_cast_pos

/-- `𝖦` is nonnegative. -/
theorem histogramGrowth_nonneg : 0 ≤ histogramGrowth := histogramGrowth_pos.le

/-- `𝖦 ^ 2 = 𝗀`. -/
theorem histogramGrowth_sq : histogramGrowth ^ 2 = (growthRatio : ℝ) := by
  rw [histogramGrowth_eq_sqrt, Real.sq_sqrt growthRatio_cast_pos.le]

/-- `𝖦 * 𝖦 = 𝗀`. -/
theorem histogramGrowth_mul_self : histogramGrowth * histogramGrowth = (growthRatio : ℝ) := by
  rw [← sq, histogramGrowth_sq]

/-- `𝖦 ^ (2 j) = 𝗀 ^ j` for every natural number `j`. -/
theorem histogramGrowth_pow_two_mul (j : ℕ) :
    histogramGrowth ^ (2 * j) = (growthRatio : ℝ) ^ j := by
  rw [pow_mul, histogramGrowth_sq]

/-- `𝖦 ^ j = 𝗀 ^ (j/2)` for every natural number `j`. -/
theorem histogramGrowth_pow_eq_rpow (j : ℕ) :
    histogramGrowth ^ j = (growthRatio : ℝ) ^ ((j : ℝ) / 2) := by
  rw [histogramGrowth_def, ← Real.rpow_natCast, ← Real.rpow_mul growthRatio_cast_pos.le]
  ring_nf

/-- `1 < 𝖦`. -/
theorem one_lt_histogramGrowth : 1 < histogramGrowth := by
  rw [histogramGrowth_eq_sqrt]
  exact Real.lt_sqrt_of_sq_lt (by rw [growthRatio_cast]; norm_num)

/-- `1 ≤ 𝖦`. -/
theorem one_le_histogramGrowth : 1 ≤ histogramGrowth := one_lt_histogramGrowth.le

/-- `202/201 < 𝖦`. -/
theorem lt_histogramGrowth : (202 / 201 : ℝ) < histogramGrowth := by
  rw [histogramGrowth_eq_sqrt]
  exact Real.lt_sqrt_of_sq_lt (by rw [growthRatio_cast]; norm_num)

/-- `1/201 < 𝖦 - 1`. -/
theorem lt_histogramGrowth_sub_one : (1 / 201 : ℝ) < histogramGrowth - 1 := by
  linarith [lt_histogramGrowth]

end CollatzPosDens
