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
$$\varsigma = \mathsf g^{-9/8} = (100/101)^{9/8},$$
where `𝗀 = 101/100` is the physical growth ratio. It satisfies `0 < ς < 1`,
`ς ^ 8 = 𝗀 ^ (-9) = (100/101) ^ 9`, and `ς ^ j = 𝗀 ^ (-9 j / 8)` for every natural number `j`.

## Main definitions

* `CollatzPosDens.deficitRate`: the real number `ς = 𝗀 ^ (-9/8)`.

## Main results

* `CollatzPosDens.deficitRate_eq`: `ς = (100/101) ^ (9/8)`.
* `CollatzPosDens.deficitRate_pos`, `CollatzPosDens.deficitRate_lt_one`: `0 < ς < 1`.
* `CollatzPosDens.deficitRate_pow_eight`: `ς ^ 8 = (100/101) ^ 9`.
* `CollatzPosDens.deficitRate_pow_eq_rpow`: `ς ^ j = 𝗀 ^ (-(9/8) j)`.

## Implementation notes

The ratio `𝗀` is rational; `ς` is defined as the real power `(𝗀 : ℝ) ^ (-9/8 : ℝ)` of its cast,
which is the positive real power of a positive real number.
-/

@[expose] public section

namespace CollatzPosDens

/-- The deficit rate `ς = 𝗀 ^ (-9/8) = (100/101) ^ (9/8) ∈ ℝ_{>0}`. -/
@[collatz_pos_dens "def_s04_varsigma"]
noncomputable def deficitRate : ℝ := (growthRatio : ℝ) ^ (-(9 / 8) : ℝ)

/-- `ς = 𝗀 ^ (-9/8)`, with `𝗀` cast to `ℝ`. -/
theorem deficitRate_def : deficitRate = (growthRatio : ℝ) ^ (-(9 / 8) : ℝ) := rfl

/-- `ς = (100/101) ^ (9/8)`. -/
theorem deficitRate_eq : deficitRate = (100 / 101 : ℝ) ^ (9 / 8 : ℝ) := by
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

/-- For every natural number `j`, `ς ^ j = 𝗀 ^ (-(9/8) j)`. -/
theorem deficitRate_pow_eq_rpow (j : ℕ) :
    deficitRate ^ j = (growthRatio : ℝ) ^ (-(9 / 8) * (j : ℝ)) := by
  rw [deficitRate_def, ← Real.rpow_natCast, ← Real.rpow_mul growthRatio_cast_pos.le]

/-- `ς ^ 8 = 𝗀 ^ (-9)`. -/
theorem deficitRate_pow_eight_eq_zpow : deficitRate ^ 8 = (growthRatio : ℝ) ^ (-9 : ℤ) := by
  rw [deficitRate_pow_eq_rpow, ← Real.rpow_intCast]
  norm_num

/-- `ς ^ 8 = (100/101) ^ 9`. -/
theorem deficitRate_pow_eight : deficitRate ^ 8 = (100 / 101 : ℝ) ^ 9 := by
  rw [deficitRate_pow_eight_eq_zpow, growthRatio_cast]
  norm_num

end CollatzPosDens
