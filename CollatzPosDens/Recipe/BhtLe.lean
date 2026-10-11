/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Texp
public import CollatzPosDens.Recipe.Bht
public import CollatzPosDens.Recipe.Erec
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.PhH0Large
public import CollatzPosDens.Recipe.PhDeltaEnclosure
public import CollatzPosDens.Recipe.JLe
public import CollatzPosDens.FirstCrossing.ScalesUpper
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Upper bound for the height exponent

For every endpoint `s ≥ 1`, the height exponent `B_ht(s) = 𝓔(J) + ⌊2 b_J/3⌋`, `J = J_*(s)`,
satisfies `B_ht(s) < 2^16 𝓜(s)^3`.

Since `t(u) ≤ 2u`, unfolding the exponent recurrence gives
`𝓔(J) ≤ 17 J + J(J-1)/64 + 2 ∑_{j<J} b_j`. The upper growth of the scales,
`b_j < 201 𝗀^j` with `𝗀 = 101/100`, turns the sum into a geometric one:
`∑_{j<J} b_j < 20100 𝗀^J`, and `⌊2 b_J/3⌋ < 134 𝗀^J`, so
`B_ht(s) < 17 J + J^2/64 + 40334 𝗀^J`. Writing `H = log₂ 𝓜(s)`, one has `𝗀^J = 2^{J δ}` with
`δ = log₂ 𝗀 < 3/200` and `J < 200 H`, hence `𝗀^J < 2^{3H} = 𝓜(s)^3`; together with
`H < 𝓜(s)` this gives `B_ht(s) < 44359 𝓜(s)^3 < 2^16 𝓜(s)^3`.

## Main results

* `CollatzPosDens.sixtyFour_mul_erec_le`: `64 𝓔(j) ≤ 1088 j + j^2 + 128 ∑_{i<j} b_i`.
* `CollatzPosDens.sum_range_scale_le`: `∑_{i<J} b_i ≤ 20100 (𝗀^J - 1)`.
* `CollatzPosDens.heightExponentOf_lt_growthRatio_pow`:
  `𝓔(J) + ⌊2 b_J/3⌋ < 17 J + J^2/64 + 40334 𝗀^J`.
* `CollatzPosDens.heightExponent_lt_two_pow_sixteen_mul_seedBound_pow_three`:
  `B_ht(s) < 2^16 𝓜(s)^3`.

## References

* [Mazur, *Collatz positive density*], Section 16.3.
-/

@[expose] public section

namespace CollatzPosDens

open Finset Real

/-- The exponent recurrence is bounded by `𝓔(j) ≤ j (17 + j + b_j)`. -/
theorem erec_le_mul_scale (j : ℕ) : erec j ≤ j * (17 + j + scale j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [erec_succ]
    have ht := texp_le_self (scale j)
    have hs : scale j ≤ scale (j + 1) := scale_monotone (Nat.le_succ j)
    have hd : j / 32 ≤ j := Nat.div_le_self _ _
    have h1 : j * (17 + j + scale j) ≤ j * (17 + (j + 1) + scale (j + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    calc erec j + 17 + j / 32 + texp (scale j)
        ≤ j * (17 + (j + 1) + scale (j + 1)) + (17 + (j + 1) + scale (j + 1)) := by omega
      _ = (j + 1) * (17 + (j + 1) + scale (j + 1)) := by ring

/-- The scales satisfy `b_j < 2^(8 + j)`. -/
theorem scale_lt_two_pow_eight_add (j : ℕ) : scale j < 2 ^ (8 + j) := by
  have h := scale_lt_mul_growthRatio_pow j
  have hg : (growthRatio : ℝ) ^ j ≤ 2 ^ j :=
    pow_le_pow_left₀ growthRatio_cast_pos.le (by rw [growthRatio_cast]; norm_num) j
  have : (scale j : ℝ) < 2 ^ (8 + j) := by
    rw [pow_add]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) j]
  exact_mod_cast this

/-- For every `J`, `𝓔(J) + ⌊2 b_J/3⌋ < 2^(9 + 2J)`. -/
theorem heightExponentOf_lt_two_pow (J : ℕ) : heightExponentOf J < 2 ^ (9 + 2 * J) := by
  rw [heightExponentOf_def]
  have he := erec_le_mul_scale J
  have hs := scale_lt_two_pow_eight_add J
  have hd : 2 * scale J / 3 ≤ scale J := by omega
  have hJ : J + 1 ≤ 2 ^ J := Nat.lt_two_pow_self
  have h8 : 17 + J ≤ 2 ^ (8 + J) := by
    rw [pow_add]
    omega
  calc erec J + 2 * scale J / 3 ≤ (J + 1) * (17 + J + scale J) := by nlinarith
    _ < 2 ^ J * (2 ^ (8 + J) + 2 ^ (8 + J)) :=
      Nat.mul_lt_mul_of_le_of_lt hJ (by omega) (by positivity)
    _ = 2 ^ (9 + 2 * J) := by ring

/-- Unfolding the exponent recurrence: `64 𝓔(j) ≤ 1088 j + j^2 + 128 ∑_{i<j} b_i`, i.e.
`𝓔(j) ≤ 17 j + j^2/64 + 2 ∑_{i<j} b_i`. -/
theorem sixtyFour_mul_erec_le (j : ℕ) :
    64 * erec j ≤ 1088 * j + j * j + 128 * ∑ i ∈ range j, scale i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [erec_succ, sum_range_succ]
    have ht := texp_le_self (scale j)
    have hd : 64 * (j / 32) ≤ 2 * j := by omega
    nlinarith

/-- The geometric sum of the scales: `∑_{i<J} b_i ≤ 20100 (𝗀^J - 1)`. -/
theorem sum_range_scale_le (J : ℕ) :
    (∑ i ∈ range J, (scale i : ℝ)) ≤ 20100 * ((growthRatio : ℝ) ^ J - 1) := by
  calc (∑ i ∈ range J, (scale i : ℝ)) ≤ ∑ i ∈ range J, 201 * (growthRatio : ℝ) ^ i :=
        sum_le_sum fun i _ => (scale_lt_mul_growthRatio_pow i).le
    _ = 201 * (((growthRatio : ℝ) ^ J - 1) / ((growthRatio : ℝ) - 1)) := by
        rw [← mul_sum, geom_sum_eq (by rw [growthRatio_cast]; norm_num)]
    _ = 20100 * ((growthRatio : ℝ) ^ J - 1) := by
        rw [growthRatio_cast]; field_simp; ring

/-- For every `J`, `𝓔(J) + ⌊2 b_J/3⌋ < 17 J + J^2/64 + 40334 𝗀^J`. -/
theorem heightExponentOf_lt_growthRatio_pow (J : ℕ) :
    (heightExponentOf J : ℝ) < 17 * J + (J : ℝ) ^ 2 / 64 + 40334 * (growthRatio : ℝ) ^ J := by
  rw [heightExponentOf_def]
  have he : (64 * erec J : ℝ) ≤ 1088 * J + J * J + 128 * ∑ i ∈ range J, (scale i : ℝ) := by
    exact_mod_cast sixtyFour_mul_erec_le J
  have hsum := sum_range_scale_le J
  have hb := scale_lt_mul_growthRatio_pow J
  have hd : ((2 * scale J / 3 : ℕ) : ℝ) * 3 ≤ 2 * scale J := by
    have : 2 * scale J / 3 * 3 ≤ 2 * scale J := Nat.div_mul_le_self _ _
    exact_mod_cast this
  have hg : 0 < (growthRatio : ℝ) ^ J := pow_pos growthRatio_cast_pos J
  push_cast
  nlinarith

/-- For a positive natural number `M`, `log₂ M < M`. -/
theorem logb_two_natCast_lt {M : ℕ} (hM : 0 < M) : logb 2 (M : ℝ) < M := by
  set n := Nat.log 2 M
  have h1 : M < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  have h2 : 2 ^ n ≤ M := Nat.pow_log_le_self 2 hM.ne'
  have h3 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h4 : logb 2 (M : ℝ) < (n + 1 : ℕ) := by
    rw [logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast hM), rpow_natCast]
    exact_mod_cast h1
  have h5 : ((n + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast h3.trans h2
  linarith

/-- For every endpoint `s ≥ 1`, `B_ht(s) < 2^16 𝓜(s)^3`. -/
@[collatz_pos_dens "lem_s04_Bht_le"]
theorem heightExponent_lt_two_pow_sixteen_mul_seedBound_pow_three {s : ℕ} (hs : 0 < s) :
    heightExponent s < 2 ^ 16 * seedBound s ^ 3 := by
  set J := finalGenerationThreshold s with hJdef
  set M : ℝ := (seedBound s : ℝ) with hMdef
  set H : ℝ := logb 2 M with hHdef
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.mpr (seedBound_pos hs)
  have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr (one_le_seedBound hs)
  have hJH : (J : ℝ) < 200 * H := finalGenerationThreshold_lt_logb_seedBound hs
  have hH : (10 : ℝ) ^ 12 < H := logb_two_seedBound_gt hs
  have hHpos : 0 < H := lt_trans (by norm_num) hH
  have hHM : H < M := logb_two_natCast_lt (seedBound_pos hs)
  have hJ0 : (0 : ℝ) ≤ J := J.cast_nonneg
  -- `𝗀^J = 2^{J δ} < 2^{3H} = 𝓜(s)^3`
  have hδ := logGrowthRate_mem_Ioo
  have hδpos := logGrowthRate_pos
  have hgJ : (growthRatio : ℝ) ^ J < M ^ 3 := by
    have e1 : (growthRatio : ℝ) ^ J = (2 : ℝ) ^ ((J : ℝ) * logGrowthRate) := by
      rw [mul_comm, rpow_mul (by norm_num), logGrowthRate,
        rpow_logb (by norm_num) (by norm_num) growthRatio_cast_pos, rpow_natCast]
    have e2 : M ^ 3 = (2 : ℝ) ^ (3 * H) := by
      rw [mul_comm, rpow_mul (by norm_num), hHdef, rpow_logb (by norm_num) (by norm_num) hM0]
      norm_cast
    rw [e1, e2]
    apply rpow_lt_rpow_of_exponent_lt (by norm_num)
    have : logGrowthRate < 3 / 200 := lt_trans hδ.2 (by norm_num)
    nlinarith
  have hB := heightExponentOf_lt_growthRatio_pow J
  rw [← heightExponent_eq_heightExponentOf] at hB
  have hM3 : M ≤ M ^ 3 := le_self_pow₀ hM1 (by norm_num)
  have hM2 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM1 (by norm_num)
  have hJ2 : (J : ℝ) ^ 2 ≤ (200 * H) ^ 2 := pow_le_pow_left₀ hJ0 hJH.le 2
  have hH2 : H ^ 2 < M ^ 2 := pow_lt_pow_left₀ hHM hHpos.le (by norm_num)
  have : (heightExponent s : ℝ) < 2 ^ 16 * M ^ 3 := by nlinarith
  rw [hMdef] at this
  exact_mod_cast this

end CollatzPosDens
