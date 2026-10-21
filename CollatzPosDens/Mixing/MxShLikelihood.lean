/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import Mathlib.Analysis.SpecialFunctions.Exp
public import CollatzPosDens.Mixing.MxShNu
public import CollatzPosDens.Mixing.MxShWidthUpper
public import CollatzPosDens.Mixing.MxShLogLower

/-!
# The likelihood of an exposed pattern

Let `n ≥ mxGateLevel = 2 ^ 80`, `N ∈ ℕ` with `3 n ≤ 2 N`, and let `M` be a real number with
`0 ≤ M ≤ N / 2 + h^sh_n + 2`. With `q = ν^sh_n`, the exposure length, we have
`M ^ q ≤ (100 / 99) 2^{-q} (N - q) ^ q`.

Writing `n = t ^ 16`, the bounds `1 ≤ log n ≤ n^{1/8}` give `1 ≤ q ≤ 2049 t ^ 2`, and
`h^sh_n ≤ 13 t ^ 9`, so `E := q (2 h^sh_n + 2 q + 4)` is at most `n / 100`; in particular
`N - q ≥ n`. Then `M ≤ (N - q) / 2 · (1 + x)` with `x = (2 h^sh_n + 2 q + 4) / (N - q)`, and
`(1 + x) ^ q ≤ exp (q x) ≤ 1 / (1 - q x) ≤ 100 / 99` since `q x ≤ 1 / 100`.

## Main results

* `CollatzPosDens.shLikelihood_le`: `M ^ q ≤ (100 / 99) (2 ^ q)⁻¹ (N - q) ^ q`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `n ≥ 2 ^ 80`, `q = ν^sh_n` and `h = h^sh_n`, the error term `q (2 h + 2 q + 4)` is at
most `n / 100`. -/
theorem shNu_mul_le {n : ℕ} (hn : 2 ^ 80 ≤ n) :
    (shNu n : ℝ) * (2 * shWidth n + 2 * shNu n + 4) ≤ n / 100 := by
  have hn' : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set t : ℝ := (n : ℝ) ^ (1 / 16 : ℝ) with ht
  have hpow : ∀ k : ℕ, (n : ℝ) ^ ((k : ℝ) / 16) = t ^ k := fun k => by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; congr 1; ring
  have h16 : (n : ℝ) = t ^ 16 := by rw [← hpow 16]; norm_num
  have h2 : (n : ℝ) ^ (1 / 8 : ℝ) = t ^ 2 := by rw [← hpow 2]; norm_num
  have h9 : (n : ℝ) ^ (9 / 16 : ℝ) = t ^ 9 := by rw [← hpow 9]; norm_num
  have ht32 : (32 : ℝ) ≤ t := by
    have : ((2 : ℝ) ^ 80) ^ (1 / 16 : ℝ) ≤ t := Real.rpow_le_rpow (by positivity) hn' (by norm_num)
    rwa [show ((2 : ℝ) ^ 80) = (2 ^ 5) ^ (16 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), show ((16 : ℕ) : ℝ) * (1 / 16) = 1 by norm_num,
      Real.rpow_one, show (2 : ℝ) ^ 5 = 32 by norm_num] at this
  have hL1 : (1 : ℝ) ≤ Real.log n :=
    le_trans (by norm_num) (le_log_of_two_pow_eighty_le (by exact_mod_cast hn))
  have hLu : Real.log n ≤ t ^ 2 := h2 ▸ log_le_rpow_one_div_eight (by exact_mod_cast hn)
  have hq : (shNu n : ℝ) ≤ 2049 * t ^ 2 := by
    have := shNu_lt_add_one n; nlinarith
  have hq0 : (0 : ℝ) ≤ shNu n := Nat.cast_nonneg _
  have hh : (shWidth n : ℝ) ≤ 13 * t ^ 9 := h9 ▸ shWidth_le_rpow hn
  have ht7 : (4098 : ℝ) * t ^ 4 + 4 * t ^ 2 ≤ t ^ 11 := by
    have h4 : (32 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht32 7
    have : (1 : ℝ) ≤ t ^ 2 := by nlinarith
    have e11 : t ^ 11 = t ^ 7 * t ^ 4 := by ring
    have e4 : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [e11]; nlinarith [pow_nonneg (le_trans (by norm_num) ht32 : (0 : ℝ) ≤ t) 4]
  have ht5 : (5532300 : ℝ) ≤ t ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) ht32 5)
  have ht0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht32
  calc (shNu n : ℝ) * (2 * shWidth n + 2 * shNu n + 4)
      ≤ 2049 * t ^ 2 * (26 * t ^ 9 + 4098 * t ^ 2 + 4) := by
        refine mul_le_mul hq (by linarith) (by positivity) (by positivity)
    _ = 2049 * (26 * t ^ 11 + (4098 * t ^ 4 + 4 * t ^ 2)) := by ring
    _ ≤ 2049 * (27 * t ^ 11) := by gcongr; linarith
    _ = 5532300 * t ^ 11 / 100 := by ring
    _ ≤ t ^ 5 * t ^ 11 / 100 := by gcongr
    _ = n / 100 := by rw [h16]; ring

/-- **The likelihood of an exposed pattern.** Let `n ≥ mxGateLevel`, `N ∈ ℕ` with
`3 n ≤ 2 N`, and `M` real with `0 ≤ M ≤ N / 2 + h^sh_n + 2`. Then, with `q = ν^sh_n`,
`M ^ q ≤ (100 / 99) 2^{-q} (N - q) ^ q`. -/
@[collatz_pos_dens "lem_mx_sh_likelihood"]
theorem shLikelihood_le {n N : ℕ} (hn : mxGateLevel ≤ n) (hN : 3 * n ≤ 2 * N) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : M ≤ N / 2 + shWidth n + 2) :
    M ^ shNu n ≤ 100 / 99 * ((2 : ℝ) ^ shNu n)⁻¹ * ((N : ℝ) - shNu n) ^ shNu n := by
  rw [mxGateLevel_def] at hn
  set q := shNu n with hqdef
  set h := shWidth n
  have hE := shNu_mul_le hn
  rw [← hqdef] at hE
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast shNu_pos (n := n) (le_trans (by norm_num) hn)
  have hn' : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hN' : (3 : ℝ) * n ≤ 2 * N := by exact_mod_cast hN
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  set D : ℝ := (N : ℝ) - q with hD
  have hqn : (q : ℝ) ≤ n / 200 := by nlinarith
  have hDn : (n : ℝ) ≤ D := by rw [hD]; linarith
  have hD0 : 0 < D := lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hn') hDn
  set x : ℝ := (2 * h + 2 * q + 4) / D with hx
  have hx0 : 0 ≤ x := by positivity
  have hqx : q * x ≤ 1 / 100 := by
    rw [hx, ← mul_div_assoc, div_le_iff₀ hD0]; nlinarith
  have hMx : M ≤ D / 2 * (1 + x) := by
    rw [hx, mul_add, mul_one, div_mul_div_comm, mul_comm (2 : ℝ) D, ← div_div,
      mul_div_cancel_left₀ _ hD0.ne']
    linarith
  have hexp : (1 + x) ^ q ≤ Real.exp (q * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) q
  have hexp2 : Real.exp (q * x) ≤ 100 / 99 := by
    have h1 : 1 - q * x ≤ Real.exp (-(q * x)) := by linarith [Real.add_one_le_exp (-(q * x))]
    have h2 : Real.exp (q * x) * Real.exp (-(q * x)) = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (q * x) := Real.exp_pos _
    nlinarith
  calc M ^ q ≤ (D / 2 * (1 + x)) ^ q := pow_le_pow_left₀ hM0 hMx q
    _ = (1 + x) ^ q * ((2 : ℝ) ^ q)⁻¹ * D ^ q := by rw [mul_pow, div_pow]; ring
    _ ≤ 100 / 99 * ((2 : ℝ) ^ q)⁻¹ * D ^ q := by
        gcongr
        exact hexp.trans hexp2

end CollatzPosDens
