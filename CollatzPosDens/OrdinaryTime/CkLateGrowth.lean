/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.Positivity

/-!
# Late growth of the scales

The scales `b_n` eventually dominate `2^{40} n`: for every integer `n ≥ 2 · 10^{10}`,
$$b_n \ge 2^{40} n.$$
By geometric growth of the scales, `b_n ≥ 𝗀^n b_0 = 9 (1 + 1/100)^n`. Keeping only the
fourth term of the binomial expansion gives `(1 + 1/100)^n ≥ \binom n4 100^{-4}`, and
`24 \binom n4 = n(n-1)(n-2)(n-3) ≥ n^4/16` once `n ≥ 6`. Hence `b_n ≥ 9 n^4 / (384 · 10^8)`,
which is at least `2^{40} n` as soon as `9 n^3 ≥ 2^{40} · 384 · 10^8`, in particular for
`n ≥ 2 · 10^{10}`.

## Main results

* `CollatzPosDens.two_pow_forty_mul_le_scale`: `2^{40} n ≤ b_n` for `n ≥ 2 · 10^{10}`.

## Implementation notes

The statement is in `ℕ`, which is the strongest form, since `b_n` is a natural number.
-/

@[expose] public section

namespace CollatzPosDens

/-- The fourth binomial term bounds `(101/100)^n` from below. -/
private theorem choose_four_le_growthRatio_pow (n : ℕ) :
    (n.choose 4 : ℝ) * (1 / 100) ^ 4 ≤ (101 / 100 : ℝ) ^ n := by
  rcases lt_or_ge n 4 with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul]; positivity
  have e : (101 / 100 : ℝ) = 1 / 100 + 1 := by norm_num
  rw [e, add_pow]
  have hm : 4 ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun m =>
    (1 / 100 : ℝ) ^ m * 1 ^ (n - m) * (n.choose m : ℝ)) (fun _ _ => by positivity) hm)
  simp only [one_pow, mul_one]; ring

/-- `n^4 ≤ 384 \binom n4` in `ℝ`, for `n ≥ 6`. -/
private theorem pow_four_le_choose_four (n : ℕ) (hn : 6 ≤ n) :
    (n : ℝ) ^ 4 ≤ 384 * (n.choose 4 : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h : (m + 6).descFactorial 4 = Nat.factorial 4 * (m + 6).choose 4 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h' : (m + 6).descFactorial 4 = (m + 6) * (m + 5) * (m + 4) * (m + 3) := by
    simp [Nat.descFactorial_succ]; ring
  have hc : ((m + 6).choose 4 : ℝ) * 24 = (m + 6) * (m + 5) * (m + 4) * (m + 3) := by
    have : (m + 6).choose 4 * 24 = (m + 6) * (m + 5) * (m + 4) * (m + 3) := by
      rw [← h', h]; simp [Nat.factorial]; ring
    exact_mod_cast this
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  push_cast
  nlinarith [hc, mul_nonneg hm hm, mul_nonneg (mul_nonneg hm hm) hm,
    mul_nonneg (mul_nonneg (mul_nonneg hm hm) hm) hm]

/-- For every integer `n ≥ 2 · 10^{10}`, the scale `b_n` is at least `2^{40} n`. -/
@[collatz_pos_dens "lem_ck_late_growth"]
theorem two_pow_forty_mul_le_scale (n : ℕ) (hn : 2 * 10 ^ 10 ≤ n) :
    2 ^ 40 * n ≤ scale n := by
  have h1 := scale_add_ge_growthRatio_pow_mul 0 n
  rw [zero_add, scale_zero, growthRatio_cast] at h1
  have h2 := choose_four_le_growthRatio_pow n
  have h3 := pow_four_le_choose_four n (by omega)
  have hn' : (2 * 10 ^ 10 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have key : (2 ^ 40 * n : ℝ) ≤ 9 * ((n : ℝ) ^ 4 / (384 * 10 ^ 8)) := by
    have hn3 : (2 * 10 ^ 10 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by gcongr
    rw [mul_div_assoc', le_div_iff₀ (by norm_num)]
    have : (n : ℝ) ^ 4 = n * n ^ 3 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hn3 hn0]
  have : (2 ^ 40 * n : ℝ) ≤ scale n := by
    refine key.trans (le_trans ?_ h1)
    have : (n : ℝ) ^ 4 / (384 * 10 ^ 8) ≤ (n.choose 4 : ℝ) * (1 / 100) ^ 4 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    nlinarith
  exact_mod_cast this

end CollatzPosDens
