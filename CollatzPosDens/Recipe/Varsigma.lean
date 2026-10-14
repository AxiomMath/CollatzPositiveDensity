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
# The deficit rate `ς`

The deficit rate of the arithmetic recipe is the positive real number
$$\varsigma = \mathsf g^{-3/2} = (100/101)^{3/2},$$
where `𝗀 = 101/100` is the physical growth ratio. It satisfies `0 < ς < 1`,
`ς ^ 2 = 𝗀 ^ (-3) = (100/101) ^ 3`, and `ς ^ j = 𝗀 ^ (-3 j / 2)` for every natural number `j`.

## Main definitions

* `CollatzPosDens.deficitRate`: the real number `ς = 𝗀 ^ (-3/2)`.

## Main results

* `CollatzPosDens.deficitRate_eq`: `ς = (100/101) ^ (3/2)`.
* `CollatzPosDens.deficitRate_pos`, `CollatzPosDens.deficitRate_lt_one`: `0 < ς < 1`.
* `CollatzPosDens.deficitRate_pow_two`: `ς ^ 2 = (100/101) ^ 3`.
* `CollatzPosDens.deficitRate_pow_eq_rpow`: `ς ^ j = 𝗀 ^ (-(3/2) j)`.

## Implementation notes

The ratio `𝗀` is rational; `ς` is defined as the real power `(𝗀 : ℝ) ^ (-3/2)` of its cast,
following [mazur2026]'s convention that powers with real exponents are positive real powers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The deficit rate `ς = 𝗀 ^ (-3/2) = (100/101) ^ (3/2) ∈ ℝ_{>0}`. -/
@[collatz_pos_dens "def_s04_varsigma"]
noncomputable def deficitRate : ℝ := (growthRatio : ℝ) ^ (-(3 / 2) : ℝ)

/-- `ς = 𝗀 ^ (-3/2)`, with `𝗀` cast to `ℝ`. -/
theorem deficitRate_def : deficitRate = (growthRatio : ℝ) ^ (-(3 / 2) : ℝ) := rfl

/-- `ς = (100/101) ^ (3/2)`. -/
theorem deficitRate_eq : deficitRate = (100 / 101 : ℝ) ^ (3 / 2 : ℝ) := by
  rw [deficitRate_def, growthRatio_cast, Real.rpow_neg (by norm_num),
    ← Real.inv_rpow (by norm_num)]
  norm_num

/-- The deficit rate is positive: `0 < ς`. -/
theorem deficitRate_pos : 0 < deficitRate :=
  Real.rpow_pos_of_pos growthRatio_cast_pos _

/-- The deficit rate is nonnegative: `0 ≤ ς`. -/
theorem deficitRate_nonneg : 0 ≤ deficitRate := deficitRate_pos.le

/-- The deficit rate is less than one: `ς < 1`. -/
theorem deficitRate_lt_one : deficitRate < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg one_lt_growthRatio_cast (by norm_num)

/-- The deficit rate is at most one: `ς ≤ 1`. -/
theorem deficitRate_le_one : deficitRate ≤ 1 := deficitRate_lt_one.le

/-- For every natural number `j`, `ς ^ j = 𝗀 ^ (-(3/2) j)`. -/
theorem deficitRate_pow_eq_rpow (j : ℕ) :
    deficitRate ^ j = (growthRatio : ℝ) ^ (-(3 / 2) * (j : ℝ)) := by
  rw [deficitRate_def, ← Real.rpow_natCast, ← Real.rpow_mul growthRatio_cast_pos.le]

/-- `ς ^ 2 = 𝗀 ^ (-3)`. -/
theorem deficitRate_pow_two_eq_zpow : deficitRate ^ 2 = (growthRatio : ℝ) ^ (-3 : ℤ) := by
  rw [deficitRate_pow_eq_rpow, ← Real.rpow_intCast]
  norm_num

/-- `ς ^ 2 = (100/101) ^ 3`. -/
theorem deficitRate_pow_two : deficitRate ^ 2 = (100 / 101 : ℝ) ^ 3 := by
  rw [deficitRate_pow_two_eq_zpow, growthRatio_cast]
  norm_num

end CollatzPosDens
