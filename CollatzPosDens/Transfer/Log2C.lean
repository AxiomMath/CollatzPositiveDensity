/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.Transfer.XHead
public import CollatzPosDens.Transfer.AtanhBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The binary logarithm of the mixing coefficient

We enclose the binary logarithm of the mixing coefficient `C = 477/20 · X_*^{A_*} + 159/10`:
$$\frac{87532002162790}{10^9} < \log_2 C < \log_2 (C + 1) < \frac{87532002162791}{10^9}.$$

Write `X_* = u · 2^k` with `k = 35007`; the leading binary digits of `X_*` place `u` in a very
short interval inside `[1, 2]`. Since `477/20 = 16 · 477/320`,
$$\log_2 C > 4 + A_* k + \frac{\log (477/320) + A_* \log u}{\log 2},$$
and `log (C + 1)` exceeds the same expression (with `u` from above) by at most
`log (1 + 338/(477 X_*^{A_*})) ≤ 338/(477 X_*^{A_*})`, which is negligible. The three logarithms
`log 2`, `log u` and `log (477/320)` are enclosed by partial sums of the inverse hyperbolic
tangent series.

## Main results

* `CollatzPosDens.logb_two_mixingConst_mem`: the enclosure of `log₂ C` and `log₂ (C + 1)`.

## Implementation notes

The bounds `u^- ≤ u ≤ u^+` coming from the leading `80` binary digits of `X_*` are first replaced
by the continued fraction convergents `195241/133188 ≤ u^-` and `u^+ ≤ 1202510/820319`, and each
series is truncated after at most `12` terms, the partial sums being rounded outward to sixteen
decimal places. The resulting enclosure of `log₂ C` still has width below `10^{-10}`, well inside
the target interval.
-/

@[expose] public section

namespace CollatzPosDens

open Real

private theorem log2C_log_two :
    (4332169878499 / 6250000000000 : ℝ) ≤ log 2 ∧
      log 2 ≤ 6931471805599463 / 10000000000000000 := by
  obtain ⟨h1, h2⟩ := log_mem_atanh_partialSum (y := (2 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

private theorem log2C_log_lower :
    (1912365144745881 / 5000000000000000 : ℝ) ≤ log (195241 / 133188) := by
  obtain ⟨h1, -⟩ := log_mem_atanh_partialSum (y := (195241 / 133188 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h1
  linarith

private theorem log2C_log_upper :
    log (1202510 / 820319) ≤ (3824730289554809 / 10000000000000000 : ℝ) := by
  obtain ⟨-, h2⟩ := log_mem_atanh_partialSum (y := (1202510 / 820319 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h2
  linarith

private theorem log2C_log_c :
    (1995977475472823 / 5000000000000000 : ℝ) ≤ log (477 / 320) ∧
      log (477 / 320) ≤ 3991954950945691 / 10000000000000000 := by
  obtain ⟨h1, h2⟩ := log_mem_atanh_partialSum (y := (477 / 320 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

private theorem log2C_Xstar_mem :
    (195241 / 133188 * 2 ^ 79 : ℝ) * 2 ^ 34928 ≤ Xstar ∧
      (Xstar : ℝ) ≤ (1202510 / 820319 * 2 ^ 79 : ℝ) * 2 ^ 34928 := by
  obtain ⟨hX1, hX2⟩ := Xstar_head
  have hP : (0 : ℝ) ≤ 2 ^ 34928 := by positivity
  have h₁ : ((886085405399619011114762 * 2 ^ 34928 : ℚ) : ℝ) ≤ Xstar := by exact_mod_cast hX1
  have h₂ : (Xstar : ℝ) < ((886085405399619011114763 * 2 ^ 34928 : ℚ) : ℝ) := by
    exact_mod_cast hX2
  push_cast at h₁ h₂
  exact ⟨(mul_le_mul_of_nonneg_right (by norm_num) hP).trans h₁,
    h₂.le.trans (mul_le_mul_of_nonneg_right (by norm_num) hP)⟩

private theorem log2C_log_Xstar :
    log (195241 / 133188) + 35007 * log 2 ≤ log Xstar ∧
      log Xstar ≤ log (1202510 / 820319) + 35007 * log 2 := by
  obtain ⟨hX1, hX2⟩ := log2C_Xstar_mem
  have h₁ := log_le_log (by positivity) hX1
  have h₂ := log_le_log (by exact_mod_cast Xstar_pos) hX2
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_pow, log_pow] at h₁ h₂
  push_cast at h₁ h₂
  constructor <;> linarith

private theorem log2C_ten_pow_le_rpow : (10 : ℝ) ^ 20 ≤ (Xstar : ℝ) ^ (Aexp : ℝ) := by
  obtain ⟨hX, -⟩ := log2C_Xstar_mem
  have hP : (1 : ℝ) ≤ 2 ^ 34928 := one_le_pow₀ (by norm_num)
  generalize (2 : ℝ) ^ 34928 = P at hX hP
  have hX1 : (1 : ℝ) ≤ Xstar := by nlinarith
  have hXR : (Xstar : ℝ) ≤ (Xstar : ℝ) ^ (Aexp : ℝ) := by
    simpa using rpow_le_rpow_of_exponent_le hX1 (show (1 : ℝ) ≤ Aexp by rw [Aexp_cast]; norm_num)
  nlinarith

/-- **Binary logarithm of the mixing coefficient.**
`87532002162790/10^9 < log₂ C < log₂ (C + 1) < 87532002162791/10^9`. -/
@[collatz_pos_dens "lem_s02_log2C"]
theorem logb_two_mixingConst_mem :
    (87532002162790 / 10 ^ 9 : ℝ) < logb 2 mixingConst ∧
      logb 2 mixingConst < logb 2 (mixingConst + 1) ∧
      logb 2 (mixingConst + 1) < 87532002162791 / 10 ^ 9 := by
  obtain ⟨l2m, l2p⟩ := log2C_log_two
  have la := log2C_log_lower
  have lb := log2C_log_upper
  obtain ⟨lcm, lcp⟩ := log2C_log_c
  obtain ⟨hlogX1, hlogX2⟩ := log2C_log_Xstar
  have hl2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hc : log (477 / 20) = 4 * log 2 + log (477 / 320) := by
    rw [show (477 / 20 : ℝ) = 2 ^ 4 * (477 / 320) by norm_num, log_mul (by positivity)
      (by positivity), log_pow]
    push_cast
    ring
  have hRbig := log2C_ten_pow_le_rpow
  set R : ℝ := (Xstar : ℝ) ^ (Aexp : ℝ) with hR
  have hRpos : 0 < R := Xstar_rpow_Aexp_pos
  have hlogR : log R = 10241 / 4096 * log Xstar := by
    rw [hR, log_rpow (by exact_mod_cast Xstar_pos), Aexp_cast]
  have hC := mixingConst_def
  rw [← hR] at hC
  have hlogC : log (477 / 20 * R) < log mixingConst :=
    log_lt_log (by positivity) (by rw [hC]; linarith)
  rw [log_mul (by norm_num) hRpos.ne', hc, hlogR] at hlogC
  have hlogC1 : log (mixingConst + 1) ≤ log (477 / 20 * R) + 338 / (477 * R) := by
    have he : mixingConst + 1 = 477 / 20 * R * (1 + 338 / (477 * R)) := by
      rw [hC]
      field_simp
      ring
    rw [he, log_mul (by positivity) (by positivity)]
    have := log_le_sub_one_of_pos (x := 1 + 338 / (477 * R)) (by positivity)
    linarith
  rw [log_mul (by norm_num) hRpos.ne', hc, hlogR] at hlogC1
  have hv : 338 / (477 * R) ≤ (1 / 10 ^ 20 : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [logb, lt_div_iff₀ hl2]
    have h := mul_le_mul_of_nonneg_left l2p
      (show (0 : ℝ) ≤ 87532002162790 / 10 ^ 9 - 4 - 10241 / 4096 * 35007 by norm_num)
    nlinarith
  · exact logb_lt_logb (by norm_num) mixingConst_pos (by linarith)
  · rw [logb, div_lt_iff₀ hl2]
    have h := mul_le_mul_of_nonneg_left l2m
      (show (0 : ℝ) ≤ 87532002162791 / 10 ^ 9 - 4 - 10241 / 4096 * 35007 by norm_num)
    nlinarith

end CollatzPosDens
