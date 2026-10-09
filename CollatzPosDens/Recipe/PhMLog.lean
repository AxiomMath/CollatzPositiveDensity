/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.Transfer.Log2C
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The logarithm of the modulus exponent

We bound the binary logarithm of the modulus exponent `m = ⌊(2^39 𝓜 C)^{8/9}⌋₊ + 1`, where
`𝓜 ≥ 1` and `C ≥ 1` are real parameters:
$$\log_2 m < \tfrac89 \log_2 \mathcal{M} + \log_2 C + 92.$$

Put `y = (2^39 𝓜 C)^{8/9}`. Since `𝓜 ≥ 1` and `C ≥ 1`, we have `y ≥ 1`, hence `m ≤ y + 1 ≤ 2 y`
and `log₂ m ≤ 1 + 8/9 (39 + log₂ 𝓜 + log₂ C)`. As `1 + 8 · 39 / 9 < 92` and `0 ≤ log₂ C`, the
bound follows.

## Main results

* `CollatzPosDens.logb_two_modulusExponent_lt`: `log₂ m < 8/9 log₂ 𝓜 + log₂ C + 92`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Logarithm of the modulus.** `log₂ m < 8/9 · log₂ 𝓜 + log₂ C + 92`. -/
@[collatz_pos_dens "lem_ph_m_log"]
theorem logb_two_modulusExponent_lt :
    logb 2 (modulusExponent : ℝ) <
      8 / 9 * logb 2 (seedBound : ℝ) + logb 2 mixingConst + 92 := by
  have hM : (1 : ℝ) ≤ seedBound := by exact_mod_cast seedBound_pos
  have hC : (1 : ℝ) ≤ mixingConst := one_le_mixingConst
  set x : ℝ := (2 : ℝ) ^ 39 * seedBound * mixingConst with hx
  have hx1 : 1 ≤ x := by
    rw [hx]
    have : (1 : ℝ) ≤ 2 ^ 39 := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul this hM zero_le_one (by positivity)]
  have hy1 : 1 ≤ x ^ (8 / 9 : ℝ) := one_le_rpow hx1 (by norm_num)
  have hm : (modulusExponent : ℝ) ≤ 2 * x ^ (8 / 9 : ℝ) := by
    have h := modulusExponent_sub_one_le
    have h1 := one_le_modulusExponent
    rw [Nat.cast_sub h1, Nat.cast_one, ← hx] at h
    linarith
  have hmpos : (0 : ℝ) < modulusExponent := by exact_mod_cast modulusExponent_pos
  have hl := logb_le_logb_of_le (b := 2) (by norm_num) hmpos hm
  rw [logb_mul (by norm_num) (by positivity), logb_self_eq_one (by norm_num),
    logb_rpow_eq_mul_logb_of_pos (by positivity), hx,
    logb_mul (by positivity) (by positivity), logb_mul (by positivity) (by positivity),
    logb_pow, logb_self_eq_one (by norm_num)] at hl
  have hlC : 0 ≤ logb 2 mixingConst := logb_nonneg (by norm_num) hC
  push_cast at hl
  linarith

end CollatzPosDens
