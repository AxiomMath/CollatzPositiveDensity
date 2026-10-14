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
$$\varrho = \mathsf g^{-1} = 100/101,$$
a fixed negative real power of the physical growth ratio `𝗀 = 101/100`. It governs the geometric
decay of the tail sums $\sum_{j \ge n} j^d \varrho^j$. It satisfies `0 < ϱ < 1` and is the
rational number `100/101`, so every numerical comparison involving `ϱ` reduces to an exact
rational one.

## Main definitions

* `CollatzPosDens.errorDecayRatio`: the real number `ϱ = 𝗀 ^ (-1)`.

## Main results

* `CollatzPosDens.errorDecayRatio_eq`: `ϱ = 100/101`.
* `CollatzPosDens.errorDecayRatio_pos`, `CollatzPosDens.errorDecayRatio_lt_one`:
  `0 < ϱ < 1`.
* `CollatzPosDens.errorDecayRatio_pow`: `ϱ ^ j = (100/101) ^ j`.
* `CollatzPosDens.errorDecayRatio_pow_eq_rpow`: `ϱ ^ j = 𝗀 ^ (-j)`.
* `CollatzPosDens.histogramGrowth_mul_deficitRate`: `𝖦 ς = ϱ`, and its `n`-th power
  `CollatzPosDens.histogramGrowth_pow_mul_deficitRate_pow`.

## Implementation notes

The ratio `𝗀` is rational; `ϱ` is defined as the real power `(𝗀 : ℝ) ^ (-1 : ℝ)` of its cast,
following [mazur2026]'s convention that powers with real exponents are positive real powers, and
in the same shape as the deficit rate `ς = 𝗀 ^ (-3/2)` and the histogram growth `𝖦 = 𝗀 ^ (1/2)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The error decay ratio `ϱ = 𝗀 ^ (-1) = 100/101 ∈ ℝ_{>0}`. -/
@[collatz_pos_dens "def_s04_varrho"]
noncomputable def errorDecayRatio : ℝ := (growthRatio : ℝ) ^ (-1 : ℝ)

/-- The error decay ratio is the real power `𝗀 ^ (-1)` of the growth ratio. -/
theorem errorDecayRatio_def : errorDecayRatio = (growthRatio : ℝ) ^ (-1 : ℝ) := rfl

/-- The error decay ratio equals `100/101`. -/
theorem errorDecayRatio_eq : errorDecayRatio = 100 / 101 := by
  rw [errorDecayRatio_def, Real.rpow_neg_one, growthRatio_cast]
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

/-- For every natural number `j`, `ϱ ^ j = (100/101) ^ j`. -/
theorem errorDecayRatio_pow (j : ℕ) : errorDecayRatio ^ j = (100 / 101 : ℝ) ^ j := by
  rw [errorDecayRatio_eq]

/-- For every natural number `j`, `ϱ ^ j = 𝗀 ^ (-j)`. -/
theorem errorDecayRatio_pow_eq_rpow (j : ℕ) :
    errorDecayRatio ^ j = (growthRatio : ℝ) ^ (-(j : ℝ)) := by
  rw [errorDecayRatio_def, ← Real.rpow_natCast, ← Real.rpow_mul growthRatio_cast_pos.le]
  ring_nf

/-- `𝖦 ς = ϱ`: the histogram growth times the deficit rate is the error decay ratio,
`g^{1/2} g^{-3/2} = g^{-1}`. -/
theorem histogramGrowth_mul_deficitRate : histogramGrowth * deficitRate = errorDecayRatio := by
  rw [histogramGrowth_def, deficitRate_def, errorDecayRatio_def,
    ← Real.rpow_add growthRatio_cast_pos]
  norm_num

/-- `𝖦^n ς^n = ϱ^n`. -/
theorem histogramGrowth_pow_mul_deficitRate_pow (n : ℕ) :
    histogramGrowth ^ n * deficitRate ^ n = errorDecayRatio ^ n := by
  rw [← mul_pow, histogramGrowth_mul_deficitRate]

end CollatzPosDens
