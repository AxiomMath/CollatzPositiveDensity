/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.LevelLateLower
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Recipe.Varsigma
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.Transfer.Log2C

/-!
# Decay of the mixing-plus-deficit bracket

Let `n ≥ 444`, let `k, k' ≥ k_n` be integers, where `k_n` is the residue level, and let `D` be a
real number with `0 ≤ D ≤ (2^121 + 1024 + 2^{-16}) ς^n`, where `ς = 𝗀^{-9/8}` is the deficit
rate. Then, with `C` the mixing coefficient,
$$C\,k^{-9/8} + C\,k'^{-9/8} + D < \tfrac{28}{1000}(C+1)\,\varsigma^n.$$

Since `k_n ≥ 47 𝗀^n`, each of `k^{-9/8}` and `k'^{-9/8}` is at most `47^{-9/8} ς^n`, and the
exact comparison `2000^8 < 27^8 · 47^9` gives `2 · 47^{-9/8} < 27/1000`. Since `log₂ C > 87532`,
the coefficient `C` is so large that `C / 1000` exceeds `2^121 + 1024 + 2^{-16}`.

## Main results

* `CollatzPosDens.bracket_decay_lt`: the strict bound above.
* `CollatzPosDens.bracket_decay_rpow_le`: `k^{-9/8} ≤ 47^{-9/8} ς^n` for `k ≥ k_n`,
  `n ≥ 444`.

## Implementation notes

The integers `k, k'` are natural numbers (they are at least `k_n ≥ 2`), and `k^{-9/8}` is the real
power `(k : ℝ) ^ (-(9/8) : ℝ)`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- For `n ≥ 444` and `k ≥ k_n`, `k^{-9/8} ≤ 47^{-9/8} ς^n`. -/
theorem bracket_decay_rpow_le {n k : ℕ} (hn : 444 ≤ n) (hk : level n ≤ k) :
    (k : ℝ) ^ (-(9 / 8) : ℝ) ≤ (47 : ℝ) ^ (-(9 / 8) : ℝ) * deficitRate ^ n := by
  have hg : 0 < (growthRatio : ℝ) := growthRatio_cast_pos
  have h47 : 47 * (growthRatio : ℝ) ^ n ≤ k :=
    (level_late_lower hn).trans (by exact_mod_cast hk)
  calc (k : ℝ) ^ (-(9 / 8) : ℝ) ≤ (47 * (growthRatio : ℝ) ^ n) ^ (-(9 / 8) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h47 (by norm_num)
    _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), deficitRate_pow_eq_rpow,
          ← Real.rpow_natCast, ← Real.rpow_mul hg.le, mul_comm (n : ℝ)]

/-- `2 · 47^{-9/8} < 27/1000`, from `2000^8 < 27^8 · 47^9`. -/
private theorem bracketDecay_two_mul_lt : 2 * (47 : ℝ) ^ (-(9 / 8) : ℝ) < 27 / 1000 := by
  set t : ℝ := (47 : ℝ) ^ (9 / 8 : ℝ) with ht
  have htpos : 0 < t := by positivity
  have ht8 : t ^ 8 = 47 ^ 9 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hlt : (2000 : ℝ) < 27 * t := by
    have h : (2000 : ℝ) ^ 8 < (27 * t) ^ 8 := by
      rw [mul_pow, ht8]
      norm_num
    exact lt_of_pow_lt_pow_left₀ 8 (by positivity) h
  rw [Real.rpow_neg (by norm_num), ← ht, ← div_eq_mul_inv, div_lt_div_iff₀ htpos (by norm_num)]
  linarith

/-- `2^121 + 1024 + 2^{-16} < C / 1000`. -/
private theorem bracketDecay_const_lt : (2 : ℝ) ^ 121 + 1024 + 2⁻¹ ^ 16 < mixingConst / 1000 := by
  have h200 : (2 : ℝ) ^ (200 : ℝ) ≤ mixingConst := by
    calc (2 : ℝ) ^ (200 : ℝ) ≤ 2 ^ (logb 2 mixingConst) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [logb_two_mixingConst_mem.1])
      _ = mixingConst := Real.rpow_logb (by norm_num) (by norm_num) mixingConst_pos
  have h200' : (2 : ℝ) ^ (200 : ℕ) ≤ mixingConst := by
    rw [← Real.rpow_natCast]
    exact_mod_cast h200
  have : (2 : ℝ) ^ 121 + 1024 + 2⁻¹ ^ 16 < 2 ^ (200 : ℕ) / 1000 := by norm_num
  linarith

/-- **Decay of the mixing-plus-deficit bracket**. For `n ≥ 444`, `k, k' ≥ k_n` and
`0 ≤ D ≤ (2^121 + 1024 + 2^{-16}) ς^n`, `C k^{-9/8} + C k'^{-9/8} + D < (28/1000) (C + 1) ς^n`. -/
@[collatz_pos_dens "lem_bracket_decay"]
theorem bracket_decay_lt {n k k' : ℕ} (hn : 444 ≤ n) (hk : level n ≤ k) (hk' : level n ≤ k')
    {D : ℝ} (_hD0 : 0 ≤ D) (hD : D ≤ (2 ^ 121 + 1024 + 2⁻¹ ^ 16) * deficitRate ^ n) :
    mixingConst * (k : ℝ) ^ (-(9 / 8) : ℝ) + mixingConst * (k' : ℝ) ^ (-(9 / 8) : ℝ) + D <
      28 / 1000 * (mixingConst + 1) * deficitRate ^ n := by
  have hC := mixingConst_pos
  have hs : 0 < deficitRate ^ n := pow_pos deficitRate_pos n
  have h1 := mul_le_mul_of_nonneg_left (bracket_decay_rpow_le hn hk) hC.le
  have h2 := mul_le_mul_of_nonneg_left (bracket_decay_rpow_le hn hk') hC.le
  set a : ℝ := (47 : ℝ) ^ (-(9 / 8) : ℝ)
  set s : ℝ := deficitRate ^ n
  set C : ℝ := mixingConst
  have e1 : C * (a * s) + C * (a * s) < 27 / 1000 * C * s := by
    have := mul_lt_mul_of_pos_right bracketDecay_two_mul_lt (mul_pos hC hs)
    linarith
  have e2 : D < C / 1000 * s := hD.trans_lt (mul_lt_mul_of_pos_right bracketDecay_const_lt hs)
  linarith

end CollatzPosDens
