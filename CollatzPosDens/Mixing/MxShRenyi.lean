/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Mixing.MxShHeight
public import CollatzPosDens.Mixing.MxShHLower
public import CollatzPosDens.Mixing.MxShHUpper
public import CollatzPosDens.Mixing.MxShSqrtBinom
public import CollatzPosDens.CharSum.ChPiUpper

/-!
# The Rényi-type sum over crossing indices

For every integer `n ≥ mxGateLevel = 2 ^ 80`, with `H = shHeight n` the crossing height of the
shell cut,
$$\sum_{i=0}^{H-1}\sqrt{\tbinom{H-1}{i}\,2^{1-H}} < 2\, n^{1/4}.$$

Put `N = H - 1`. The linear bounds on the crossing height give `1 ≤ N < (317/200) n`. The
square-root binomial bound and `π < 22/7` give
`(∑ √(C(N, i) 2^{-N}))^2 ≤ 4 + π √N < 4 + (22/7) √(317/200) √n`. Since
`(22/7)^2 · 317/200 < (399/100)^2` and `4 ≤ √n / 100`, the square is less than `4 √n`; taking
square roots gives the claim.

## Main results

* `CollatzPosDens.sum_range_sqrt_choose_shHeight_lt`: the displayed bound.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- **Rényi-type sum over crossing indices**: for `n ≥ mxGateLevel`, with `H = shHeight n`,
`∑_{i=0}^{H-1} √(C(H-1, i) 2^{1-H}) < 2 n^{1/4}`. -/
@[collatz_pos_dens "lem_mx_sh_renyi"]
theorem sum_range_sqrt_choose_shHeight_lt {n : ℕ} (hn : mxGateLevel ≤ n) :
    ∑ i ∈ range (shHeight n),
        √(((shHeight n - 1).choose i : ℝ) * (2 : ℝ) ^ (1 - (shHeight n : ℤ))) <
      2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [mxGateLevel_def] at hn
  set H := shHeight n with hHdef
  have hnR : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hlow := shHeight_lower n
  have hup := shHeight_lt_linear n
  rw [← hHdef] at hlow hup
  have hH2 : 2 ≤ H := by
    have : (2 : ℝ) ≤ H := by nlinarith
    exact_mod_cast this
  set N := H - 1 with hNdef
  have hHN : H = N + 1 := by omega
  have hN1 : 1 ≤ N := by omega
  have hNR : (N : ℝ) < 317 / 200 * n := by
    have : (H : ℝ) = N + 1 := by exact_mod_cast hHN
    linarith
  have hz : (2 : ℝ) ^ (1 - (H : ℤ)) = 1 / 2 ^ N := by
    rw [hHN, Nat.cast_add, Nat.cast_one, show (1 : ℤ) - (N + 1) = -(N : ℤ) by ring, zpow_neg,
      zpow_natCast, one_div]
  have hsum : ∑ i ∈ range H, √((N.choose i : ℝ) * (2 : ℝ) ^ (1 - (H : ℤ))) =
      ∑ i ∈ range (N + 1), √((N.choose i : ℝ) / 2 ^ N) := by
    rw [hz, ← hHN]
    simp only [mul_one_div]
  rw [hsum]
  set S := ∑ i ∈ range (N + 1), √((N.choose i : ℝ) / 2 ^ N) with hS
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => sqrt_nonneg _
  have hsq := sq_sum_range_sqrt_choose_div_two_pow_le hN1
  rw [← hS] at hsq
  have hsqrtN : √(N : ℝ) < √(317 / 200) * √n := by
    rw [← sqrt_mul (by norm_num)]
    exact sqrt_lt_sqrt (Nat.cast_nonneg _) hNR
  have hc : 22 / 7 * √(317 / 200 : ℝ) < 399 / 100 := by
    rw [show (22 / 7 : ℝ) = √((22 / 7) ^ 2) by rw [sqrt_sq (by norm_num)],
      ← sqrt_mul (by norm_num), show (399 / 100 : ℝ) = √((399 / 100) ^ 2) by
        rw [sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsn0 : 0 ≤ √(n : ℝ) := sqrt_nonneg _
  have hpi : π * √(N : ℝ) < 399 / 100 * √n := by
    have h1 : π * √(N : ℝ) ≤ 22 / 7 * √N :=
      mul_le_mul_of_nonneg_right pi_lt_twentyTwo_div_seven.le (sqrt_nonneg _)
    have h2 : 22 / 7 * √(N : ℝ) < 22 / 7 * (√(317 / 200) * √n) := by linarith
    nlinarith
  have h400 : (400 : ℝ) ≤ √n := by
    rw [Real.le_sqrt (by norm_num) hn0.le]
    nlinarith
  have hS2 : S ^ 2 < 4 * √n := by linarith
  have hq : (2 * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = 4 * √n := by
    rw [mul_pow, ← rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 4)), ← rpow_mul hn0.le, sqrt_eq_rpow]
    norm_num
  rw [← hq] at hS2
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hS2

end CollatzPosDens
