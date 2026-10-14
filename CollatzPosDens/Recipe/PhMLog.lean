/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Recipe.PhH0Large
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.Transfer.Log2C
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The modulus is below the seed allowance

For every endpoint `s ≥ 1`, the modulus exponent
`m(s) = ⌊(2^39 𝓜(s) C)^{2/3}⌋₊ + 1` is smaller than the seed bound `𝓜(s)`.

Put `y = (2^39 𝓜(s) C)^{2/3}`. Since `𝓜(s) ≥ 1` and `C ≥ 1`, we have `y ≥ 1`, hence
`m(s) ≤ y + 1 ≤ 2 y` and
`log₂ m(s) ≤ 1 + 2/3 (39 + log₂ 𝓜(s) + log₂ C) < 2/3 log₂ 𝓜(s) + log₂ C + 92`.
As `log₂ C < 87533` and `log₂ 𝓜(s) > 10 ^ 12`, the right-hand side is below `log₂ 𝓜(s)`,
so `m(s) < 𝓜(s)`.

## Main results

* `CollatzPosDens.logb_two_modulusExponent_lt`:
  `log₂ m(s) < 2/3 log₂ 𝓜(s) + log₂ C + 92`.
* `CollatzPosDens.modulusExponent_lt_seedBound`: `m(s) < 𝓜(s)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- `log₂ m(s) < 2/3 · log₂ 𝓜(s) + log₂ C + 92` for `s ≥ 1`. -/
theorem logb_two_modulusExponent_lt {s : ℕ} (hs : 0 < s) :
    logb 2 (modulusExponent s : ℝ) <
      2 / 3 * logb 2 (seedBound s : ℝ) + logb 2 mixingConst + 92 := by
  have hM : (1 : ℝ) ≤ seedBound s := by exact_mod_cast seedBound_pos hs
  have hC : (1 : ℝ) ≤ mixingConst := one_le_mixingConst
  set x : ℝ := (2 : ℝ) ^ 39 * seedBound s * mixingConst with hx
  have hx1 : 1 ≤ x := by
    rw [hx]
    have : (1 : ℝ) ≤ 2 ^ 39 := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul this hM zero_le_one (by positivity)]
  have hy1 : 1 ≤ x ^ (2 / 3 : ℝ) := one_le_rpow hx1 (by norm_num)
  have hm : (modulusExponent s : ℝ) ≤ 2 * x ^ (2 / 3 : ℝ) := by
    have h := modulusExponent_sub_one_le s
    have h1 := one_le_modulusExponent s
    rw [Nat.cast_sub h1, Nat.cast_one, ← hx] at h
    linarith
  have hmpos : (0 : ℝ) < modulusExponent s := by exact_mod_cast modulusExponent_pos s
  have hl := logb_le_logb_of_le (b := 2) (by norm_num) hmpos hm
  rw [logb_mul (by norm_num) (by positivity), logb_self_eq_one (by norm_num),
    logb_rpow_eq_mul_logb_of_pos (by positivity), hx,
    logb_mul (by positivity) (by positivity), logb_mul (by positivity) (by positivity),
    logb_pow, logb_self_eq_one (by norm_num)] at hl
  have hlC : 0 ≤ logb 2 mixingConst := logb_nonneg (by norm_num) hC
  push_cast at hl
  linarith

/-- **The modulus is below the seed allowance.** `m(s) < 𝓜(s)` for every `s ≥ 1`. -/
@[collatz_pos_dens "lem_ph_m_log"]
theorem modulusExponent_lt_seedBound {s : ℕ} (hs : 0 < s) :
    modulusExponent s < seedBound s := by
  have hl := logb_two_modulusExponent_lt hs
  have hC := (logb_two_mixingConst_mem).2.1.trans (logb_two_mixingConst_mem).2.2
  have hH := logb_two_seedBound_gt hs
  have hlt : logb 2 (modulusExponent s : ℝ) < logb 2 (seedBound s : ℝ) := by
    have : logb 2 mixingConst < 87533 := by linarith
    nlinarith
  have hmpos : (0 : ℝ) < modulusExponent s := by exact_mod_cast modulusExponent_pos s
  have hMpos : (0 : ℝ) < seedBound s := by exact_mod_cast seedBound_pos hs
  exact_mod_cast (logb_lt_logb_iff (by norm_num) hmpos hMpos).1 hlt

end CollatzPosDens
