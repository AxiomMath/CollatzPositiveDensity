/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.Recipe.PhBlockLen
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.FirstCrossing.ScalesLateLower
public import CollatzPosDens.FirstCrossing.ScalesUpper
public import CollatzPosDens.OrdinaryTime.CkWidthLate
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The length sum up to generation `N_*`

Let `b_j` be the scales (`b_0 = 16544`, `b_{j+1} = b_j + ⌈b_j/100⌉`), `k_n = ⌊b_n/4⌋` the residue
levels, `len⁺` the block length and `𝗀 = 101/100` the growth ratio. We show
`k_{N_*} + ∑_{j<N_*} len⁺(b_j) < 1668728 𝗀^{N_*}`.

Write `N = N_*`. The block length satisfies `len⁺(b) ≤ h_b ≤ 8b/5` always, and
`len⁺(b) ≤ (20001/20000) b` once `b ≥ 2^40`. Since `𝗀 b_t ≤ b_{t+1}`, telescoping gives
`∑_{j<N} b_j < 100 b_N`, so the terms with `b_j ≥ 2^40` contribute less than `(100 + 1/200) b_N`.
The terms with `b_j < 2^40` are the first few scales, all below `2^40`, and the same telescoping
bounds their sum by `100 · 2^41`; as `b_N ≥ 2^57`, their contribution is below `b_N / 200`.
With `k_N ≤ b_N / 4` the total is below `(20052/200) b_N`, and `b_N < 16644 𝗀^N` concludes, as
`(20052/200) · 16644 ≤ 1668728`.

## Main results

* `CollatzPosDens.level_add_sum_lenPlus_lt`: the bound for every `N ≥ 5700`.
* `CollatzPosDens.level_generationThreshold_add_sum_lenPlus_lt`: the bound at `N = N_*`.

## Implementation notes

The estimate holds for every `N ≥ 5700`, so it is proved in that generality and instantiated at
`N_* = 9853`. The early terms (those with `b_j < 2^40`) are bounded by the telescoping
inequality `∑_{j<n, b_j<2^40} b_j ≤ 100 min(b_n, 2^41)` instead of a geometric series below
`b_L` for the last early index `L`. The lower bound `b_N ≥ 2^57` comes from `b_N ≥ 16544 𝗀^N` and
`𝗀^{100} ≥ 2` (Bernoulli), weaker than the `b_N > 16544 · 2^{140}` available at `N_*` but enough
for the early part.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- One step of the scales in integer form: `101 b_t ≤ 100 b_{t+1}`. -/
theorem hundred_one_mul_scale_le (t : ℕ) : 101 * scale t ≤ 100 * scale (t + 1) := by
  rw [scale_succ, eb_eq]
  omega

/-- Telescoping the growth of the scales: `∑_{j<n} b_j + 100 b_0 ≤ 100 b_n`. -/
theorem sum_range_scale_add_le (n : ℕ) :
    ∑ j ∈ range n, scale j + 100 * scale 0 ≤ 100 * scale n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have := hundred_one_mul_scale_le n
    omega

/-- Telescoping over the scales below `2^40`: `∑_{j<n, b_j<2^40} b_j ≤ 100 min(b_n, 2^41)`. -/
theorem sum_filter_scale_lt_two_pow_forty_le (n : ℕ) :
    ∑ j ∈ (range n).filter (fun j => scale j < 2 ^ 40), scale j ≤
      100 * min (scale n) (2 ^ 41) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_add_one, filter_insert]
    have hstep : scale (n + 1) = scale n + (scale n + 99) / 100 := by rw [scale_succ, eb_eq]
    split_ifs with h
    · rw [sum_insert (by simp)]
      omega
    · omega

/-- The scales reach `2^57` by generation `5700`. -/
theorem two_pow_fifty_seven_le_scale {N : ℕ} (hN : 5700 ≤ N) : 2 ^ 57 ≤ scale N := by
  have hg : (2 : ℝ) ≤ (growthRatio : ℝ) ^ 100 := by
    have := one_add_mul_le_pow (a := (1 / 100 : ℝ)) (by norm_num) 100
    rw [growthRatio_cast]
    norm_num at this ⊢
  have hg1 : (1 : ℝ) ≤ growthRatio := by rw [growthRatio_cast]; norm_num
  have hpow : (2 : ℝ) ^ 57 ≤ (growthRatio : ℝ) ^ N :=
    calc (2 : ℝ) ^ 57 ≤ ((growthRatio : ℝ) ^ 100) ^ 57 := pow_le_pow_left₀ (by norm_num) hg 57
      _ = (growthRatio : ℝ) ^ 5700 := by rw [← pow_mul]
      _ ≤ (growthRatio : ℝ) ^ N := pow_le_pow_right₀ hg1 hN
  have h := scale_late_lower N
  have h' : (2 : ℝ) ^ 57 ≤ scale N := by
    have : (0 : ℝ) ≤ (growthRatio : ℝ) ^ N := by positivity
    nlinarith
  exact_mod_cast h'

/-- `5 len⁺(b) ≤ 8 b` for every `b`. -/
theorem five_mul_lenPlus_le (b : ℕ) : 5 * lenPlus b ≤ 8 * b := by
  have h1 := lenPlus_le_hb b
  have h2 := five_mul_wb_le b
  rw [hb_def] at h1
  omega

/-- `20000 len⁺(b) ≤ 20001 b` for `b ≥ 2^40`. -/
theorem twenty_thousand_mul_lenPlus_le {b : ℕ} (hb : 2 ^ 40 ≤ b) :
    20000 * lenPlus b ≤ 20001 * b := by
  rw [lenPlus_of_le hb]
  have := twenty_thousand_mul_wd_le hb
  omega

/-- Integer form of the length bound: `4·10^6 (k_N + ∑_{j<N} len⁺(b_j)) < 401040000 b_N`
for `N ≥ 5700`. -/
theorem level_add_sum_lenPlus_lt_aux {N : ℕ} (hN : 5700 ≤ N) :
    4000000 * (level N + ∑ j ∈ range N, lenPlus (scale j)) < 401040000 * scale N := by
  have hsplit := sum_filter_add_sum_filter_not (range N) (fun j => scale j < 2 ^ 40)
    (fun j => lenPlus (scale j))
  -- the early part
  have hE : 5 * ∑ j ∈ (range N).filter (fun j => scale j < 2 ^ 40), lenPlus (scale j) ≤
      8 * (100 * min (scale N) (2 ^ 41)) := by
    refine le_trans ?_ (Nat.mul_le_mul_left 8 (sum_filter_scale_lt_two_pow_forty_le N))
    rw [mul_sum, mul_sum]
    exact sum_le_sum fun j _ => five_mul_lenPlus_le _
  -- the late part
  have hT : 20000 * ∑ j ∈ (range N).filter (fun j => ¬ scale j < 2 ^ 40), lenPlus (scale j) ≤
      20001 * ∑ j ∈ range N, scale j := by
    rw [mul_sum, mul_sum]
    calc ∑ j ∈ (range N).filter (fun j => ¬ scale j < 2 ^ 40), 20000 * lenPlus (scale j)
        ≤ ∑ j ∈ (range N).filter (fun j => ¬ scale j < 2 ^ 40), 20001 * scale j := by
          refine sum_le_sum fun j hj => twenty_thousand_mul_lenPlus_le ?_
          exact not_lt.1 (mem_filter.1 hj).2
      _ ≤ ∑ j ∈ range N, 20001 * scale j := sum_le_sum_of_subset (filter_subset _ _)
  have hS := sum_range_scale_add_le N
  have hL := four_mul_level_le N
  have hb := two_pow_fifty_seven_le_scale hN
  rw [← hsplit]
  omega

/-- **The length bound for large `N`.** For every `N ≥ 5700`,
`k_N + ∑_{j<N} len⁺(b_j) < 1668728 𝗀^N`. -/
theorem level_add_sum_lenPlus_lt {N : ℕ} (hN : 5700 ≤ N) :
    ((level N + ∑ j ∈ range N, lenPlus (scale j) : ℕ) : ℝ) <
      1668728 * (growthRatio : ℝ) ^ N := by
  have h1 : ((4000000 * (level N + ∑ j ∈ range N, lenPlus (scale j)) : ℕ) : ℝ) <
      ((401040000 * scale N : ℕ) : ℝ) := by
    exact_mod_cast level_add_sum_lenPlus_lt_aux hN
  have h2 := scale_lt_mul_growthRatio_pow N
  have h3 : 0 < (growthRatio : ℝ) ^ N := pow_pos growthRatio_cast_pos N
  push_cast at h1 ⊢
  nlinarith

/-- The generation threshold is at least `5700`. -/
theorem le_generationThreshold_5700 : 5700 ≤ generationThreshold := by
  rw [generationThreshold_def]; decide

/-- The length sum up to generation `N_*` is bounded:
`k_{N_*} + ∑_{j<N_*} len⁺(b_j) < 1668728 𝗀^{N_*}`. -/
@[collatz_pos_dens "lem_s04_qstar_ge"]
theorem level_generationThreshold_add_sum_lenPlus_lt :
    ((level generationThreshold +
        ∑ j ∈ range generationThreshold, lenPlus (scale j) : ℕ) : ℝ) <
      1668728 * (growthRatio : ℝ) ^ generationThreshold :=
  level_add_sum_lenPlus_lt le_generationThreshold_5700

end CollatzPosDens
