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

For every natural number `n ≥ 2^131072` the upper window end
`mxWindowHigh n = ⌈mxLevel n / 2 + n^{2049/4096} / 4⌉` satisfies `16 · mxWindowHigh n < 13 n`.

Indeed `mxLevel n < n log₂ 3 ≤ (317/200) n`, since the logarithmic correction is positive for
`n ≥ 1`; and `n^{2047/4096} ≥ 25` gives `n^{2049/4096} / 4 = n / (4 n^{2047/4096}) ≤ n / 100`.
Since `⌈x⌉ < x + 1` and `1 ≤ n / 100`,
`mxWindowHigh n < (317/400) n + n/100 + n/100 = (13/16) n`.

## Main results

* `CollatzPosDens.mxWindowHigh_bound`: `16 · mxWindowHigh n < 13 n` for `n ≥ 2^131072`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The upper window end is small: `16 · mxWindowHigh n < 13 n` for every `n ≥ 2^131072`. -/
@[collatz_pos_dens "lem_mx_window_high_bound"]
theorem mxWindowHigh_bound (n : ℕ) (hn : 2 ^ 131072 ≤ n) :
    16 * mxWindowHigh n < 13 * (n : ℤ) := by
  have hn' : (2 : ℕ) ^ 4096 ≤ n :=
    (pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 4096 ≤ 131072)).trans hn
  have hnR : ((2 : ℝ) ^ (4096 : ℝ)) ≤ (n : ℝ) := by
    have e : (2 : ℝ) ^ (4096 : ℝ) = (2 : ℝ) ^ (4096 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [e]
    exact_mod_cast hn'
  have hpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have h1 : (1 : ℝ) ≤ n := by
    have : (1 : ℕ) ≤ n := le_trans Nat.one_le_two_pow hn'
    exact_mod_cast this
  have h100 : (100 : ℝ) ≤ n := by
    have : (100 : ℕ) ≤ n := le_trans (le_trans (by norm_num : 100 ≤ 2 ^ 7)
      (pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 7 ≤ 4096))) hn'
    exact_mod_cast this
  have h25 : (25 : ℝ) ≤ (n : ℝ) ^ ((2047 : ℝ) / 4096) := by
    have hmono := Real.rpow_le_rpow (by positivity) hnR (by norm_num : (0 : ℝ) ≤ 2047 / 4096)
    rw [← Real.rpow_mul (by norm_num)] at hmono
    refine le_trans ?_ hmono
    have : (2 : ℝ) ^ (5 : ℝ) ≤ (2 : ℝ) ^ ((4096 : ℝ) * (2047 / 4096)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    refine le_trans ?_ this
    norm_num
  have hsplit : (n : ℝ) ^ ((2049 : ℝ) / 4096) * (n : ℝ) ^ ((2047 : ℝ) / 4096) = n := by
    rw [← Real.rpow_add hpos]; norm_num
  have hroot : (1 / 4 : ℝ) * (n : ℝ) ^ ((2049 : ℝ) / 4096) ≤ n / 100 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h25 h0]
  have hlog : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) h1
  have hlev : mxLevel n < 317 / 200 * n := by
    rw [mxLevel_def]
    nlinarith [logb_two_three_bounds.2]
  have hq := mxWindowHigh_lt n
  generalize (n : ℝ) ^ ((2049 : ℝ) / 4096) = r at hq hroot
  have : (16 * mxWindowHigh n : ℝ) < 13 * (n : ℝ) := by
    linarith only [hq, hroot, hlev, h100]
  exact_mod_cast this

end CollatzPosDens
