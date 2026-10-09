/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The logarithmic growth rate `δ`

The logarithmic growth rate associated with the growth ratio `CollatzPosDens.growthRatio`,
`𝗀 = 101/100`, is
$$\delta = \log_2 \mathsf g = \log_2 (101/100) \in \mathbb{R}_{>0}.$$

## Main definitions

* `CollatzPosDens.logGrowthRate`: the logarithmic growth rate `δ = log₂ 𝗀`.

## Main results

* `CollatzPosDens.logGrowthRate_def`: `δ = log₂ (101/100)`.
* `CollatzPosDens.logGrowthRate_pos`: `0 < δ`.
* `CollatzPosDens.rpow_logGrowthRate`: `2 ^ δ = 𝗀`.

## Implementation notes

`δ` is a plain real constant rather than an element of the subtype `ℝ_{>0}`, so that it can be
used directly in real arithmetic; the membership `δ ∈ ℝ_{>0}` is the lemma `logGrowthRate_pos`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The logarithmic growth rate `δ = log₂ 𝗀 = log₂ (101/100)`. -/
@[collatz_pos_dens "def_ph_delta"]
noncomputable def logGrowthRate : ℝ := Real.logb 2 (growthRatio : ℝ)

/-- The logarithmic growth rate is `δ = log₂ (101/100)`. -/
theorem logGrowthRate_def : logGrowthRate = Real.logb 2 (101 / 100) := by
  rw [logGrowthRate, growthRatio_cast]

/-- The logarithmic growth rate is positive: `δ ∈ ℝ_{>0}`. -/
@[collatz_pos_dens "def_ph_delta"]
theorem logGrowthRate_pos : 0 < logGrowthRate :=
  Real.logb_pos (by norm_num) one_lt_growthRatio_cast

/-- Raising `2` to the logarithmic growth rate recovers the growth ratio: `2 ^ δ = 𝗀`. -/
theorem rpow_logGrowthRate : (2 : ℝ) ^ logGrowthRate = growthRatio :=
  Real.rpow_logb (by norm_num) (by norm_num) growthRatio_cast_pos

end CollatzPosDens
