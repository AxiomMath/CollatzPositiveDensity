/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06CountHeight
public import CollatzPosDens.Terminal.S06CountLog

/-!
# The census allowance of the count is small

For every integer `t ≥ 1`, writing `n = n_ct(t)` (`CollatzPosDens.countLevel`) and
`B = B_ct(t)` (`CollatzPosDens.countHeight`), and `a = a_mx(o) = 18693/10000`,
$$44\, t\Bigl(2 n^{-8} + \frac{2^{13}\sqrt{n \log n}}{B} + 2^{365} n^{-a} \log n\Bigr) < 2^{-32}.$$
With `x = x_ct(t)` and `h = 1 + log t`, one has `x^a = 2^{420} t h`, `n ≥ x ≥ 1` and
`log n ≤ 2^8 h`. The mixing term is at most `2^{-47}/t` since `n^{-a} ≤ x^{-a}`; the central
term is at most `2^{-419}/t` since `n^8 ≥ x^8 ≥ x^a ≥ 2^{420} t`; and the width term equals
`2^{-39}/t`. Summing, the left side is below `44 (2 · 2^{-47} + 2^{-39}) < 2^{-32}`.

## Main results

* `CollatzPosDens.countAllowance_lt`: the displayed inequality, for `t ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The numerical inequality
`44 (2 · 2^{-420} + 2^{13} 2^{-52} + 2^{365} 2^8 2^{-420}) < 2^{-32}`. -/
private theorem countAllowance_numeric :
    (44 : ℝ) * (2 * (2 ^ 420)⁻¹ + 2 ^ 13 * (2 ^ 52)⁻¹ + 2 ^ 365 * (2 ^ 8 * (2 ^ 420)⁻¹)) <
      2 ^ (-32 : ℤ) := by
  have h1 : (2 : ℝ) ^ 365 * (2 ^ 8 * (2 ^ 420)⁻¹) = (2 ^ 47)⁻¹ := by
    rw [show (2 : ℝ) ^ 420 = 2 ^ 365 * 2 ^ 8 * 2 ^ 47 by rw [← pow_add, ← pow_add]]
    field_simp
  have h2 : (2 : ℝ) * (2 ^ 420)⁻¹ ≤ (2 ^ 47)⁻¹ := by
    rw [show (2 : ℝ) ^ 420 = 2 * 2 ^ 419 by rw [← pow_succ'], mul_inv, ← mul_assoc,
      mul_inv_cancel₀ two_ne_zero, one_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  rw [h1]
  calc (44 : ℝ) * (2 * (2 ^ 420)⁻¹ + 2 ^ 13 * (2 ^ 52)⁻¹ + (2 ^ 47)⁻¹)
      ≤ 44 * ((2 ^ 47)⁻¹ + 2 ^ 13 * (2 ^ 52)⁻¹ + (2 ^ 47)⁻¹) := by gcongr
    _ < 2 ^ (-32 : ℤ) := by norm_num

/-- The census allowance of the count is small: for every `t ≥ 1`, with `n = n_ct(t)` and
`B = B_ct(t)`, `44 t (2 n^{-8} + 2^{13} √(n log n) / B + 2^{365} n^{-a_mx(o)} log n) < 2^{-32}`
(positive real power `n^{-a_mx(o)}`). -/
@[collatz_pos_dens "lem_s06_count_allowance"]
theorem countAllowance_lt {t : ℕ} (ht : 1 ≤ t) :
    44 * (t : ℝ) * (2 * (countLevel t : ℝ) ^ (-8 : ℤ) +
        2 ^ 13 * √((countLevel t : ℝ) * Real.log (countLevel t)) / countHeight t +
        2 ^ 365 * (countLevel t : ℝ) ^ (-(amix .o : ℝ)) * Real.log (countLevel t)) <
      2 ^ (-32 : ℤ) := by
  set n : ℝ := (countLevel t : ℝ) with hn_def
  set L : ℝ := Real.log (countLevel t : ℝ) with hL_def
  set h : ℝ := 1 + Real.log t with hh_def
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hy := Real.log_natCast_nonneg t
  have hh : 1 ≤ h := by rw [hh_def]; linarith
  have hx1 := one_le_countX ht
  have hxn : countX t ≤ n := countX_le_countLevel t
  have hn0 : 0 < n := by linarith
  have hL0 : 0 < L := log_countLevel_pos ht
  have hLle : L ≤ 256 * h := log_countLevel_le ht
  have ha : (amix .o : ℝ) = 18693 / 10000 := amix_cast_o
  have hX : countX t ^ (amix .o : ℝ) = 2 ^ 420 * t * h := countX_rpow_amix t
  set P : ℝ := n ^ (-(amix .o : ℝ)) with hP_def
  have hP0 : 0 ≤ P := Real.rpow_nonneg hn0.le _
  have hPX : P * (2 ^ 420 * t * h) ≤ 1 := by
    rw [hP_def, Real.rpow_neg hn0.le, ← hX]
    have hxa : 0 < countX t ^ (amix .o : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hle : countX t ^ (amix .o : ℝ) ≤ n ^ (amix .o : ℝ) :=
      Real.rpow_le_rpow (by linarith) hxn (by rw [ha]; norm_num)
    rw [inv_mul_le_one₀ (hxa.trans_le hle)]
    exact hle
  have hmix : (t : ℝ) * P * L ≤ 2 ^ 8 * (2 ^ 420)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (t : ℝ) * P * L * 2 ^ 420 ≤ t * P * (256 * h) * 2 ^ 420 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLle (by positivity))
          (by positivity)
      _ = 2 ^ 8 * (P * (2 ^ 420 * t * h)) := by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num]; ac_rfl
      _ ≤ 2 ^ 8 * 1 := by gcongr
      _ = 2 ^ 8 := mul_one _
  have hn8 : 2 ^ 420 * (t : ℝ) ≤ n ^ 8 := by
    calc 2 ^ 420 * (t : ℝ) ≤ 2 ^ 420 * t * h := le_mul_of_one_le_right (by positivity) hh
      _ = countX t ^ (amix .o : ℝ) := hX.symm
      _ ≤ countX t ^ ((8 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by rw [ha]; norm_num)
      _ = countX t ^ 8 := Real.rpow_natCast _ _
      _ ≤ n ^ 8 := by gcongr
  have hcen : (t : ℝ) * n ^ (-8 : ℤ) ≤ (2 ^ 420)⁻¹ := by
    rw [zpow_neg, mul_inv_le_iff₀ (by positivity), inv_mul_eq_div,
      le_div_iff₀ (by positivity), mul_comm]
    exact hn8
  have hs : 0 < √(n * L) := Real.sqrt_pos.mpr (by positivity)
  have hwid : (t : ℝ) * (√(n * L) / countHeight t) = (2 ^ 52)⁻¹ := by
    rw [countHeight_def, ← hn_def, ← hL_def]
    field_simp
  have key : 44 * (t : ℝ) * (2 * n ^ (-8 : ℤ) + 2 ^ 13 * √(n * L) / countHeight t +
      2 ^ 365 * P * L) = 44 * (2 * ((t : ℝ) * n ^ (-8 : ℤ)) +
        2 ^ 13 * ((t : ℝ) * (√(n * L) / countHeight t)) + 2 ^ 365 * ((t : ℝ) * P * L)) := by
    generalize (2 : ℝ) ^ 365 = c
    ring
  rw [key, hwid]
  calc 44 * (2 * ((t : ℝ) * n ^ (-8 : ℤ)) + 2 ^ 13 * (2 ^ 52)⁻¹ + 2 ^ 365 * ((t : ℝ) * P * L))
      ≤ 44 * (2 * (2 ^ 420)⁻¹ + 2 ^ 13 * (2 ^ 52)⁻¹ + 2 ^ 365 * (2 ^ 8 * (2 ^ 420)⁻¹)) := by
        gcongr
    _ < 2 ^ (-32 : ℤ) := countAllowance_numeric

end CollatzPosDens
