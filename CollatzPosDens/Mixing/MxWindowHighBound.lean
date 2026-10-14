/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxLevel
public import CollatzPosDens.Mixing.MxWindowHigh
public import CollatzPosDens.Transfer.Log3Bounds

/-!
# The upper window end is small

For every integer `n ≥ 2^80000` the upper window end satisfies `16 q^+_n < 13 n`.

Indeed `Lv_n < n log₂ 3 ≤ (317/200) n`, since the logarithmic correction is positive for
`n ≥ 1`; and `n^{2047/4096} ≥ 25` gives `n^{2049/4096} / 4 = n / (4 n^{2047/4096}) ≤ n / 100`.
Since `⌈x⌉ < x + 1` and `1 ≤ n / 100`,
`q^+_n < (317/400) n + n/100 + n/100 = (13/16) n`.

## Main results

* `CollatzPosDens.mxWindowHigh_bound`: `16 q^+_n < 13 n` for `n ≥ 2^80000`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The upper window end is small: `16 q^+_n < 13 n` for every `n ≥ 2^80000`. -/
@[collatz_pos_dens "lem_mx_window_high_bound"]
theorem mxWindowHigh_bound (n : ℕ) (hn : 2 ^ 80000 ≤ n) :
    16 * mxWindowHigh n < 13 * (n : ℤ) := by
  have hn' : (2 : ℕ) ^ 4096 ≤ n :=
    (pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 4096 ≤ 80000)).trans hn
  have hnR : ((2 : ℝ) ^ (4096 : ℝ)) ≤ (n : ℝ) := by
    have e : (2 : ℝ) ^ (4096 : ℝ) = (2 : ℝ) ^ (4096 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [e]
    exact_mod_cast hn'
  have h100 : (100 : ℝ) ≤ n := by
    exact_mod_cast ((by norm_num : 100 ≤ 2 ^ 7).trans
      (pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 7 ≤ 4096))).trans hn'
  have h1 : (1 : ℝ) ≤ n := by linarith only [h100]
  have hpos : (0 : ℝ) < n := by linarith only [h100]
  -- `n ^ (2047/4096) ≥ 25`
  have h25 : (25 : ℝ) ≤ (n : ℝ) ^ ((2047 : ℝ) / 4096) := by
    have hmono := Real.rpow_le_rpow (by positivity) hnR (by norm_num : (0 : ℝ) ≤ 2047 / 4096)
    rw [← Real.rpow_mul (by norm_num)] at hmono
    refine le_trans ?_ (le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by norm_num : (5 : ℝ) ≤ 4096 * (2047 / 4096))) hmono)
    norm_num
  have hsplit : (n : ℝ) ^ ((2049 : ℝ) / 4096) * (n : ℝ) ^ ((2047 : ℝ) / 4096) = n := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hroot : (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) ≤ n / 100 := by
    nlinarith [mul_le_mul_of_nonneg_left h25
      (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096))]
  have hlog : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) h1
  have hlev : mxLevel n < 317 / 200 * n := by
    rw [mxLevel_def]
    nlinarith [logb_two_three_bounds.2]
  have hq := mxWindowHigh_lt n
  generalize (n : ℝ) ^ ((2049 : ℝ) / 4096) = r at hq hroot
  exact_mod_cast (by linarith only [hq, hroot, hlev, h100] :
    (16 * mxWindowHigh n : ℝ) < 13 * (n : ℝ))

end CollatzPosDens
