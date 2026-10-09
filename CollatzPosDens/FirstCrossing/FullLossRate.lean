/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Recipe.Varsigma
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.FcCapRate
public import CollatzPosDens.FirstCrossing.ScalesGrowth

/-!
# Decay of the full-family loss

The loss of the full first-crossing family at scale `n` is bounded by
`2^{140} b_n^{-6} + 2^{-(K_n+1)}`. Both terms decay at least at the deficit rate
`ς = 𝗀^{-9/8}`: for every `n`,
$$2^{140} b_n^{-6} + 2^{-(K_n+1)} \le (2^{121} + 2^{-16})\,\varsigma^n.$$
The first term uses `b_n ≥ 9 𝗀^n` and `𝗀^{-6} ≤ ς`, together with `9^6 > 2^{19}`;
the second is the decay of the cap term.

## Main results

* `CollatzPosDens.full_loss_rate_le`: for every `n`,
  `2^{140} b_n^{-6} + 2^{-(K_n+1)} ≤ (2^{121} + 2^{-16}) ς^n`.

## Implementation notes

The negative powers are integer powers `zpow` of real numbers. The comparison `𝗀^{-6} ≤ ς`
is made as `(100/101)^6 ≤ (100/101)^{9/8}`, using the explicit form of `ς`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.6
-/

@[expose] public section

namespace CollatzPosDens

/-- `(100/101)^6 ≤ ς`, i.e. `𝗀^{-6} ≤ 𝗀^{-9/8}`. -/
theorem full_loss_rate_le_aux : (100 / 101 : ℝ) ^ 6 ≤ deficitRate := by
  rw [deficitRate_eq, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)

/-- **Decay of the full-family loss.** For every `n`,
`2^{140} b_n^{-6} + 2^{-(K_n+1)} ≤ (2^{121} + 2^{-16}) ς^n`. -/
@[collatz_pos_dens "lem_full_loss_rate"]
theorem full_loss_rate_le (n : ℕ) :
    (2 : ℝ) ^ (140 : ℕ) * (scale n : ℝ) ^ (-6 : ℤ) + (2 : ℝ) ^ (-((cap n : ℤ) + 1)) ≤
      ((2 : ℝ) ^ (121 : ℕ) + (2 : ℝ) ^ (-16 : ℤ)) * deficitRate ^ n := by
  have hcap := two_zpow_neg_cap_succ_le n
  have hb : (growthRatio : ℝ) ^ n * 9 ≤ scale n := by
    simpa using scale_add_ge_growthRatio_pow_mul 0 n
  rw [growthRatio_cast] at hb
  have hς : ((100 / 101 : ℝ) ^ 6) ^ n ≤ deficitRate ^ n :=
    pow_le_pow_left₀ (by positivity) full_loss_rate_le_aux n
  have hprod : ((100 / 101 : ℝ) ^ 6) ^ n * (((101 / 100 : ℝ) ^ n) ^ 6) = 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm 6 n, ← mul_pow]; norm_num
  have hsix : ((101 / 100 : ℝ) ^ n * 9) ^ 6 ≤ (scale n : ℝ) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hb 6
  have hspos : (0 : ℝ) < (scale n : ℝ) ^ 6 := lt_of_lt_of_le (by positivity) hsix
  have hmain : (2 : ℝ) ^ (140 : ℕ) * (scale n : ℝ) ^ (-6 : ℤ) ≤
      (2 : ℝ) ^ (121 : ℕ) * deficitRate ^ n := by
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, div_le_iff₀ hspos]
    calc (2 : ℝ) ^ (140 : ℕ)
        = 2 ^ 121 * 2 ^ 19 * (((100 / 101 : ℝ) ^ 6) ^ n * (((101 / 100 : ℝ) ^ n) ^ 6)) := by
          rw [hprod]; norm_num
      _ ≤ 2 ^ 121 * 9 ^ 6 * (deficitRate ^ n * (((101 / 100 : ℝ) ^ n) ^ 6)) := by
          gcongr; norm_num
      _ = 2 ^ 121 * deficitRate ^ n * ((101 / 100 : ℝ) ^ n * 9) ^ 6 := by ring
      _ ≤ 2 ^ 121 * deficitRate ^ n * (scale n : ℝ) ^ 6 := by
          gcongr; exact mul_nonneg (by positivity) (pow_nonneg deficitRate_nonneg _)
  linarith [add_mul ((2 : ℝ) ^ (121 : ℕ)) ((2 : ℝ) ^ (-16 : ℤ)) (deficitRate ^ n)]

end CollatzPosDens
