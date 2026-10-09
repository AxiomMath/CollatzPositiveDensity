/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.X0
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.PhLogH0
public import CollatzPosDens.Recipe.BhtLe
public import CollatzPosDens.Recipe.QstarGe
public import CollatzPosDens.Recipe.PhH0Large
public import CollatzPosDens.Recipe.PhLog23Enclosure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The cutoff chain

We prove `log₂ log₂ log₂ log₂ (1024 X_0) < log₂ q_* + 1`, where `X_0` is the cutoff and `q_*`
the conductor.

Write `h_0 = log₂ 𝓜 = 2 (19 + 3 ^ q_*)`, a natural number, so that `𝓜 = 2 ^ h_0`. Then
`1024 X_0 = 2 ^ 15 (2 ^ (B_ht + h_0) + 1) ≤ 2 ^ (16 + B_ht + h_0)`, whence
`Y_1 = log₂ (1024 X_0) ≤ 16 + B_ht + h_0 < 2 ^ (2101 h_0)` using `B_ht < 2 ^ (2100 h_0)`.
So `Y_2 = log₂ Y_1 < 2101 h_0`, and `Y_3 = log₂ Y_2 < log₂ 2101 + log₂ h_0 < 14 + q_* log₂ 3`.
As `log₂ 3 < 8/5` and `q_* ≥ 9 N_* ≥ 35`, `Y_3 < 2 q_*`, and `log₂ Y_3 < 1 + log₂ q_*`.
The lower bounds `Y_1 ≥ 16`, `Y_2 ≥ 4` keep every logarithm in the range where it is monotone.

## Main results

* `CollatzPosDens.logb_logb_logb_logb_cutoff_lt`:
  `log₂ log₂ log₂ log₂ (1024 X_0) < log₂ q_* + 1`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- If `x ≤ 2 ^ n` with `0 < x`, then `log₂ x ≤ n`. -/
theorem logb_two_le_of_le_two_pow {x : ℝ} {n : ℕ} (hx : 0 < x) (h : x ≤ 2 ^ n) :
    logb 2 x ≤ n := by
  have := logb_le_logb_of_le (b := 2) (by norm_num) hx h
  rwa [logb_pow, logb_self_eq_one (by norm_num), mul_one] at this

/-- If `x < 2 ^ n` with `0 < x`, then `log₂ x < n`. -/
theorem logb_two_lt_of_lt_two_pow {x : ℝ} {n : ℕ} (hx : 0 < x) (h : x < 2 ^ n) :
    logb 2 x < n := by
  have := logb_lt_logb (b := 2) (by norm_num) hx h
  rwa [logb_pow, logb_self_eq_one (by norm_num), mul_one] at this

/-- If `2 ^ n ≤ x`, then `n ≤ log₂ x`. -/
theorem le_logb_two_of_two_pow_le {x : ℝ} {n : ℕ} (h : (2 : ℝ) ^ n ≤ x) :
    (n : ℝ) ≤ logb 2 x := by
  have := logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
  rwa [logb_pow, logb_self_eq_one (by norm_num), mul_one] at this

/-- If `1 ≤ H` and `B < 2 ^ (2100 H)`, then `16 + B + H < 2 ^ (2101 H)`. -/
theorem sixteen_add_add_lt_two_pow_mul {B H : ℕ} (hH : 1 ≤ H) (hB : B < 2 ^ (2100 * H)) :
    16 + B + H < 2 ^ (2101 * H) := by
  have h1 : H < 2 ^ H := Nat.lt_two_pow_self
  have h2 : 2 ^ (H + 5) ≤ 2 ^ (2100 * H) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (2101 * H) = 2 ^ (2100 * H) * 2 ^ H := by
    rw [← pow_add]
    ring_nf
  have h4 : 2 ^ (H + 5) = 2 ^ H * 32 := by
    rw [pow_add]
    norm_num
  have h5 : 2 ≤ 2 ^ H := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) hH
  rw [h4] at h2
  rw [h3]
  generalize 2 ^ (2100 * H) = P at hB h2 ⊢
  generalize 2 ^ H = X at h1 h2 h5 ⊢
  nlinarith

/-- If `4 ≤ Y < 2101 h`, `log₂ h ≤ 2 + q log₂ 3` and `35 ≤ q`, then
`log₂ log₂ Y < log₂ q + 1`. -/
theorem logb_logb_lt_logb_add_one {Y h q : ℝ} (hY : 4 ≤ Y) (hYh : Y < 2101 * h) (hh : 0 < h)
    (hlog : logb 2 h ≤ 2 + q * logb 2 3) (hq : 35 ≤ q) :
    logb 2 (logb 2 Y) < logb 2 q + 1 := by
  have hl3 := logb_two_three_mem_Ioo.2
  have h2101 : logb 2 (2101 : ℝ) < 12 := by
    rw [logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    norm_num
  have hu : logb 2 Y < 2 * q := by
    have := logb_lt_logb (b := 2) (by norm_num) (by linarith) hYh
    rw [logb_mul (by norm_num) hh.ne'] at this
    nlinarith
  have := logb_lt_logb (b := 2) (by norm_num) (logb_pos (by norm_num) (by linarith)) hu
  rw [logb_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by linarith) : q ≠ 0),
    logb_self_eq_one (by norm_num)] at this
  linarith

/-- Four iterated base-2 logarithms of `1024 * cutoff` are less than `logb 2 conductor + 1`. -/
@[collatz_pos_dens "lem_ph_cutoff_chain"]
theorem logb_logb_logb_logb_cutoff_lt :
    logb 2 (logb 2 (logb 2 (logb 2 (1024 * cutoff : ℝ)))) < logb 2 conductor + 1 := by
  set H : ℕ := 2 * (19 + 3 ^ conductor) with hH
  set B : ℕ := heightExponent with hBdef
  clear_value H B
  have hH1 : 1 ≤ H := Nat.succ_le_of_lt (by rw [hH]; positivity)
  have hM : logb 2 (seedBound : ℝ) = H := by
    rw [logb_two_seedBound_eq, hH]
    push_cast
    ring
  have hMnat : seedBound = 2 ^ H := by
    rw [seedBound_def, hH, pow_mul]
    norm_num
  have hB : B < 2 ^ (2100 * H) := by
    rcases Nat.eq_zero_or_pos B with h0 | hpos
    · rw [h0]
      positivity
    · have h := logb_two_heightExponent_lt
      rw [hM, ← hBdef, logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast hpos)] at h
      have : (B : ℝ) < (2 : ℝ) ^ (2100 * H) := by
        rw [← rpow_natCast]
        push_cast
        exact h
      exact_mod_cast this
  have hX : 1024 * cutoff = 2 ^ 15 * (2 ^ (B + H) + 1) := by
    rw [cutoff_def, ← hBdef, hMnat, pow_add]
    ring
  have hXu : 1024 * cutoff ≤ 2 ^ (16 + B + H) := by
    rw [hX, show 16 + B + H = 16 + (B + H) by ring, pow_add (a := 2) 16]
    have : 1 ≤ 2 ^ (B + H) := Nat.one_le_two_pow
    generalize 2 ^ (B + H) = E at this ⊢
    omega
  have hXl : 2 ^ 16 ≤ 1024 * cutoff := by
    rw [hX]
    have : 1 ≤ 2 ^ (B + H) := Nat.one_le_two_pow
    generalize 2 ^ (B + H) = E at this ⊢
    omega
  have hY1u : logb 2 (1024 * cutoff : ℝ) ≤ ((16 + B + H : ℕ) : ℝ) :=
    logb_two_le_of_le_two_pow
      ((by positivity : (0 : ℝ) < 2 ^ 16).trans_le (by exact_mod_cast hXl))
      (by exact_mod_cast hXu)
  have hY1l : 16 ≤ logb 2 (1024 * cutoff : ℝ) := by
    exact_mod_cast le_logb_two_of_two_pow_le (x := 1024 * cutoff) (n := 16)
      (by exact_mod_cast hXl)
  have hY1 : logb 2 (1024 * cutoff : ℝ) < 2 ^ (2101 * H) :=
    hY1u.trans_lt (by exact_mod_cast sixteen_add_add_lt_two_pow_mul hH1 hB)
  have hY2u : logb 2 (logb 2 (1024 * cutoff : ℝ)) < 2101 * H := by
    exact_mod_cast logb_two_lt_of_lt_two_pow (by linarith) hY1
  have hY2l : 4 ≤ logb 2 (logb 2 (1024 * cutoff : ℝ)) := by
    exact_mod_cast le_logb_two_of_two_pow_le (x := logb 2 (1024 * cutoff)) (n := 4)
      (hY1l.trans' (by norm_num))
  have hq : (35 : ℝ) ≤ conductor := by
    exact_mod_cast (le_conductor.trans' (by norm_num) : 35 ≤ conductor)
  have hlogH : logb 2 (H : ℝ) ≤ 2 + conductor * logb 2 3 := by
    rw [← hM]
    exact logb_logb_seedBound_le
  exact logb_logb_lt_logb_add_one hY2l hY2u (by exact_mod_cast hH1) hlogH hq

end CollatzPosDens
