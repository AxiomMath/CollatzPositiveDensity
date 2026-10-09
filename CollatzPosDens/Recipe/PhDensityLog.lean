/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CM
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.PhH0Large
public import CollatzPosDens.Recipe.PhMLog
public import CollatzPosDens.Transfer.Log2C
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The logarithm of the density constant

We bound the binary logarithm of the reciprocal density constant by the seed bound:
$$\log_2(1/c_{\mathrm{M}}) < 5 \log_2 \mathcal{M}.$$

Write `h₀ = log₂ 𝓜` and `ℓ_C = log₂ C`. By definition of `c_M`,
`log₂ (1/c_M) = 33 + h₀ + (5633/2048) log₂ m`, and `0 ≤ log₂ m`. Since
`log₂ m < (8/9) h₀ + ℓ_C + 92` and `5633/2048 < 3`,
`log₂ (1/c_M) < 33 + h₀ + 3 ((8/9) h₀ + ℓ_C + 92) = (11/3) h₀ + 3 ℓ_C + 309 < 5 h₀`,
because `ℓ_C < 87533` and `h₀ > 10^12`.

## Main results

* `CollatzPosDens.logb_inv_densityConst_lt_five_mul`: `log₂ c_M⁻¹ < 5 log₂ 𝓜`.

## Implementation notes

`1/c_M` is written `c_M⁻¹`, and `log₂` is `Real.logb 2`, with `𝓜` cast to `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Logarithm of the density constant.** `log₂ (1/c_M) < 5 log₂ 𝓜`. -/
@[collatz_pos_dens "lem_ph_density_log"]
theorem logb_inv_densityConst_lt_five_mul :
    logb 2 densityConst⁻¹ < 5 * logb 2 (seedBound : ℝ) := by
  rw [logb_inv_densityConst]
  have hm := logb_two_modulusExponent_lt
  have hh := logb_two_seedBound_gt
  have hC := (logb_two_mixingConst_mem).1
  have hC' := (logb_two_mixingConst_mem).2
  have hm0 : 0 ≤ logb 2 (modulusExponent : ℝ) :=
    logb_nonneg (by norm_num) (by exact_mod_cast one_le_modulusExponent)
  have hC2 : logb 2 mixingConst < 87533 := by
    linarith [hC'.1, hC'.2]
  have hC0 : 0 ≤ logb 2 mixingConst := by linarith
  linarith

end CollatzPosDens
