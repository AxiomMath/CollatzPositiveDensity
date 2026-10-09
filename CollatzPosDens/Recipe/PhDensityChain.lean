/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CM
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.PhDensityLog
public import CollatzPosDens.Recipe.PhLogH0
public import CollatzPosDens.Recipe.PhLog23Enclosure
public import CollatzPosDens.Recipe.PhH0Large
public import CollatzPosDens.Recipe.QstarGe
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The triple logarithm of the density constant

We bound the threefold iterated binary logarithm of the reciprocal density constant by the
conductor:
$$\log_2\log_2\log_2(1/c_{\mathrm{M}}) < \log_2 q_* + 1.$$

Put `Y₁ = log₂ (1/c_M) ≥ 33` and `h₀ = log₂ 𝓜`. Since `Y₁ < 5 h₀`, the number
`Y₂ = log₂ Y₁` satisfies `Y₂ < log₂ 5 + log₂ h₀ < 3 + 2 + q_* log₂ 3`. As `log₂ 3 < 8/5`
and `q_* ≥ 9 N_* ≥ 25`, we get `0 < Y₂ < 5 + (8/5) q_* ≤ 2 q_*`, hence
`log₂ Y₂ < 1 + log₂ q_*`.

## Main results

* `CollatzPosDens.logb_logb_logb_inv_densityConst_lt`:
  `log₂ log₂ log₂ c_M⁻¹ < log₂ q_* + 1`.

## Implementation notes

`1/c_M` is written `c_M⁻¹`, `log₂` is `Real.logb 2`, and `q_*` is cast to `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The threefold iterated binary logarithm of the reciprocal density constant is less than
`log₂ q_* + 1`. -/
@[collatz_pos_dens "lem_ph_density_chain"]
theorem logb_logb_logb_inv_densityConst_lt :
    logb 2 (logb 2 (logb 2 densityConst⁻¹)) < logb 2 (conductor : ℝ) + 1 := by
  have hY1 : (33 : ℝ) ≤ logb 2 densityConst⁻¹ := by
    have h := logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
      two_pow_33_le_inv_densityConst
    rw [logb_pow, logb_self_eq_one (by norm_num)] at h
    push_cast at h
    linarith
  have hY1lt := logb_inv_densityConst_lt_five_mul
  have hh0 := logb_two_seedBound_gt
  have hh0pos : 0 < logb 2 (seedBound : ℝ) := by linarith
  have hY2lt : logb 2 (logb 2 densityConst⁻¹) <
      logb 2 5 + logb 2 (logb 2 (seedBound : ℝ)) := by
    rw [← logb_mul (by norm_num) hh0pos.ne']
    exact logb_lt_logb (by norm_num) (by linarith) hY1lt
  have h5 : logb 2 5 < 3 := by
    rw [logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    norm_num
  have hlog3 := logb_two_three_mem_Ioo.2
  have hq : (25 : ℝ) ≤ conductor := by
    have := le_conductor
    exact_mod_cast (show 25 ≤ conductor by omega)
  have hH := logb_logb_seedBound_le
  calc logb 2 (logb 2 (logb 2 densityConst⁻¹)) < logb 2 (2 * (conductor : ℝ)) :=
        logb_lt_logb (by norm_num) (logb_pos (by norm_num) (by linarith)) (by nlinarith)
    _ = logb 2 (conductor : ℝ) + 1 := by
        rw [logb_mul (by norm_num) (by linarith), logb_self_eq_one (by norm_num)]
        ring

end CollatzPosDens
