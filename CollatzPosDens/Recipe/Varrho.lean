/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Recipe.Growth
public import CollatzPosDens.Recipe.Varsigma
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The error decay ratio `ϱ`

The error decay ratio of the arithmetic recipe is the positive real number
$$\varrho = \mathsf g^{-5/8} = (100/101)^{5/8},$$
a fixed negative real power of the physical growth ratio `𝗀 = 101/100`. It governs the geometric
decay of the tail sums $\sum_{j \ge n} j^d \varrho^j$. It satisfies `0 < ϱ < 1` and
`ϱ ^ 8 = 𝗀 ^ (-5) = (100/101)^5`, so every numerical comparison involving `ϱ` reduces to an
exact rational one.

## Main definitions

* `CollatzPosDens.errorDecayRatio`: the real number `ϱ = 𝗀 ^ (-5/8)`.

## Main results

* `CollatzPosDens.errorDecayRatio_eq`: `ϱ = (100/101) ^ (5/8)`.
* `CollatzPosDens.errorDecayRatio_pos`, `CollatzPosDens.errorDecayRatio_lt_one`:
  `0 < ϱ < 1`.
* `CollatzPosDens.errorDecayRatio_pow_eight`: `ϱ ^ 8 = (100/101) ^ 5`.
* `CollatzPosDens.errorDecayRatio_pow_eq_rpow`: `ϱ ^ j = 𝗀 ^ (-(5 j)/8)`.
* `CollatzPosDens.histogramGrowth_mul_deficitRate`: `𝖦 ς = ϱ`, and its `n`-th power
  `CollatzPosDens.histogramGrowth_pow_mul_deficitRate_pow`.

## Implementation notes

The ratio `𝗀` is rational; `ϱ` is defined as the real power `(𝗀 : ℝ) ^ (-(5/8) : ℝ)` of its cast,
so that a power with a real exponent is the positive real power of a positive real number.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The error decay ratio `ϱ = 𝗀 ^ (-5/8) = (100/101) ^ (5/8) ∈ ℝ_{>0}`. -/
@[collatz_pos_dens "def_s04_varrho"]
noncomputable def errorDecayRatio : ℝ := (growthRatio : ℝ) ^ (-(5 / 8) : ℝ)

/-- The error decay ratio is the real power `𝗀 ^ (-5/8)` of the growth ratio. -/
theorem errorDecayRatio_def : errorDecayRatio = (growthRatio : ℝ) ^ (-(5 / 8) : ℝ) := rfl

/-- The error decay ratio equals `(100/101) ^ (5/8)`. -/
theorem errorDecayRatio_eq : errorDecayRatio = (100 / 101 : ℝ) ^ (5 / 8 : ℝ) := by
  rw [errorDecayRatio_def, growthRatio_cast, Real.rpow_neg (by norm_num),
    ← Real.inv_rpow (by norm_num)]
  norm_num

/-- The error decay ratio is positive. -/
theorem errorDecayRatio_pos : 0 < errorDecayRatio :=
  Real.rpow_pos_of_pos growthRatio_cast_pos _

/-- The error decay ratio is nonnegative. -/
theorem errorDecayRatio_nonneg : 0 ≤ errorDecayRatio := errorDecayRatio_pos.le

/-- The error decay ratio is strictly less than `1`. -/
theorem errorDecayRatio_lt_one : errorDecayRatio < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_growthRatio_cast (by norm_num)

/-- The error decay ratio is at most `1`. -/
theorem errorDecayRatio_le_one : errorDecayRatio ≤ 1 := errorDecayRatio_lt_one.le

/-- For every natural number `j`, `ϱ ^ j = 𝗀 ^ (-(5 j)/8)`. -/
theorem errorDecayRatio_pow_eq_rpow (j : ℕ) :
    errorDecayRatio ^ j = (growthRatio : ℝ) ^ (-(5 * (j : ℝ)) / 8) := by
  rw [errorDecayRatio_def, ← Real.rpow_natCast, ← Real.rpow_mul growthRatio_cast_pos.le]
  ring_nf

/-- The eighth power of the error decay ratio is `(100/101) ^ 5`. -/
theorem errorDecayRatio_pow_eight : errorDecayRatio ^ 8 = (100 / 101 : ℝ) ^ 5 := by
  rw [errorDecayRatio_pow_eq_rpow, growthRatio_cast]
  push_cast
  rw [show (-(5 * (8 : ℝ)) / 8) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
    Real.rpow_natCast]
  norm_num

/-- `𝖦 ς = ϱ`: the histogram growth times the deficit rate is the error decay ratio,
`g^{1/2} g^{-9/8} = g^{-5/8}`. -/
theorem histogramGrowth_mul_deficitRate : histogramGrowth * deficitRate = errorDecayRatio := by
  rw [histogramGrowth_def, deficitRate_def, errorDecayRatio_def,
    ← Real.rpow_add growthRatio_cast_pos]
  norm_num

/-- `𝖦^n ς^n = ϱ^n`. -/
theorem histogramGrowth_pow_mul_deficitRate_pow (n : ℕ) :
    histogramGrowth ^ n * deficitRate ^ n = errorDecayRatio ^ n := by
  rw [← mul_pow, histogramGrowth_mul_deficitRate]

end CollatzPosDens
