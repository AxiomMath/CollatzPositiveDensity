/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Recipe.Clog
public import CollatzPosDens.Recipe.Growth
public import CollatzPosDens.Seed.DepthWidth
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.DwUpper
public import CollatzPosDens.FirstCrossing.ScalesUpper
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Growth of the depth-width sums

For every integer `n ≥ 10000`,
$$2 \sum_{j < n} \mathrm{dw}(b_j) + 1 < 4075 \sqrt n\, \mathsf G^n,$$
where `b_j` are the scales, `dw` is the depth half-width and `𝖦 = 𝗀^{1/2}` with `𝗀 = 101/100`.

The proof combines `dw(b) ≤ ⌈√(32 b lg b)⌉` with the upper growth `b_j < 201 𝗀^j` of the scales.
Since `201 < 2^8` and `𝗀^{69} < 2`, one gets `lg(b_j) ≤ 9 + j/69`, so for `j < n` and `n ≥ 10000`,
`32 b_j lg(b_j) < 32 · 201 𝗀^j · n/64 ≤ (81/8)^2 n 𝗀^j`, that is
`dw(b_j) < (81/8) √n 𝖦^j + 1`. Summing the geometric series with `𝖦 - 1 > 1/201` gives
`∑_{j<n} dw(b_j) < (81 · 201/8) √n 𝖦^n + n`, and `n ≤ √n 𝖦^n` because `𝗀^n ≥ n`.

## Main results

* `CollatzPosDens.two_mul_sum_dw_scale_add_one_lt_lg_scale_le`:
  `lg(b_j) ≤ 9 + j/69`.
* `CollatzPosDens.two_mul_sum_dw_scale_add_one_lt`: the bound on `2 ∑_{j<n} dw(b_j) + 1`.

## Implementation notes

The inequality is stated in `ℝ`, with the natural-number depth half-widths cast to `ℝ`.
The intermediate bound `n ≤ 𝗀^n` is obtained from `𝗀^{3k} ≥ (1 + k/100)^3` with `k = ⌊n/3⌋`
(Bernoulli's inequality) rather than from the cubic binomial term.
-/

@[expose] public section

namespace CollatzPosDens

/-- `lg(b_j) ≤ 9 + j/69`: the binary ceiling-logarithm of the scales grows at most like `j/69`. -/
theorem two_mul_sum_dw_scale_add_one_lt_lg_scale_le (j : ℕ) :
    (lg (scale j) : ℝ) ≤ 9 + (j : ℝ) / 69 := by
  set k := j / 69 with hk
  have hjk : j < 69 * (k + 1) := by omega
  have hg1 : (1 : ℝ) ≤ (growthRatio : ℝ) := one_lt_growthRatio_cast.le
  have h69 : (growthRatio : ℝ) ^ 69 < 2 := by rw [growthRatio_cast]; norm_num
  have hlt : (scale j : ℝ) < (2 : ℝ) ^ (k + 9) := by
    calc (scale j : ℝ) < 201 * (growthRatio : ℝ) ^ j := scale_lt_mul_growthRatio_pow j
      _ ≤ 201 * (growthRatio : ℝ) ^ (69 * (k + 1)) := by
          gcongr 201 * ?_
          exact pow_le_pow_right₀ hg1 hjk.le
      _ = 201 * ((growthRatio : ℝ) ^ 69) ^ (k + 1) := by rw [pow_mul]
      _ ≤ 201 * 2 ^ (k + 1) := by gcongr
      _ < 2 ^ 8 * 2 ^ (k + 1) := by gcongr; norm_num
      _ = 2 ^ (k + 9) := by rw [← pow_add]; ring_nf
  have hle : lg (scale j) ≤ k + 9 :=
    lg_le_of_le_two_pow (by exact_mod_cast hlt.le)
  have hkj : (k : ℝ) ≤ (j : ℝ) / 69 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : k * 69 ≤ j)
  have hleR : (lg (scale j) : ℝ) ≤ k + 9 := by exact_mod_cast hle
  linarith

/-- `n ≤ 𝗀^n` for `n ≥ 10000`. -/
private theorem le_growthRatio_pow {n : ℕ} (hn : 10000 ≤ n) :
    (n : ℝ) ≤ (growthRatio : ℝ) ^ n := by
  set k := n / 3 with hk
  have hnk : n ≤ 3 * k + 2 := by omega
  have hk0 : 3333 ≤ k := by omega
  have hg1 : (1 : ℝ) ≤ (growthRatio : ℝ) := one_lt_growthRatio_cast.le
  have hb : 1 + (k : ℝ) * (1 / 100) ≤ (growthRatio : ℝ) ^ k := by
    rw [growthRatio_cast, show (101 / 100 : ℝ) = 1 + 1 / 100 by norm_num]
    exact one_add_mul_le_pow (by norm_num) k
  have hkR : (3333 : ℝ) ≤ k := by exact_mod_cast hk0
  have hnR : (n : ℝ) ≤ 3 * k + 2 := by exact_mod_cast hnk
  have hk2 : (3333 : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by gcongr
  have hk3 : (n : ℝ) ≤ ((k : ℝ) / 100) ^ 3 := by
    have : (k : ℝ) * 3333 ^ 2 ≤ (k : ℝ) * (k : ℝ) ^ 2 := by gcongr
    nlinarith
  calc (n : ℝ) ≤ (1 + (k : ℝ) * (1 / 100)) ^ 3 := by
        refine hk3.trans ?_
        gcongr
        linarith
    _ ≤ ((growthRatio : ℝ) ^ k) ^ 3 := by gcongr
    _ = (growthRatio : ℝ) ^ (3 * k) := by rw [← pow_mul, mul_comm]
    _ ≤ (growthRatio : ℝ) ^ n := pow_le_pow_right₀ hg1 (by omega)

/-- For `j < n` with `n ≥ 10000`, `dw(b_j) < (81/8) √n 𝖦^j + 1`. -/
theorem dw_scale_lt_sqrt_mul_histogramGrowth_pow {n j : ℕ} (hn : 10000 ≤ n) (hjn : j < n) :
    (dw (scale j) : ℝ) < 81 / 8 * √(n : ℝ) * histogramGrowth ^ j + 1 := by
  have hG0 : 0 ≤ histogramGrowth := histogramGrowth_nonneg
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn.le
  have hb := scale_lt_mul_growthRatio_pow j
  have hb0 : (0 : ℝ) ≤ scale j := Nat.cast_nonneg _
  have hlg := two_mul_sum_dw_scale_add_one_lt_lg_scale_le j
  have hlg0 : (0 : ℝ) ≤ lg (scale j) := Nat.cast_nonneg _
  have hlgn : (lg (scale j) : ℝ) ≤ n / 64 := by linarith
  have hgj : (growthRatio : ℝ) ^ j = (histogramGrowth ^ j) ^ 2 := by
    rw [← pow_mul, mul_comm, histogramGrowth_pow_two_mul]
  have hgj0 : (0 : ℝ) ≤ (growthRatio : ℝ) ^ j := (pow_pos growthRatio_cast_pos j).le
  have hroot : √(32 * (scale j : ℝ) * (lg (scale j) : ℝ)) ≤
      81 / 8 * √(n : ℝ) * histogramGrowth ^ j := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, hsqsq, ← hgj]
    calc 32 * (scale j : ℝ) * (lg (scale j) : ℝ)
        ≤ 32 * (201 * (growthRatio : ℝ) ^ j) * (n / 64) := by gcongr
      _ ≤ (81 / 8) ^ 2 * n * (growthRatio : ℝ) ^ j := by nlinarith
  calc (dw (scale j) : ℝ) ≤ (⌈√(32 * (scale j : ℝ) * (lg (scale j) : ℝ))⌉₊ : ℝ) := by
        exact_mod_cast dw_le_ceil_sqrt (scale j)
    _ < √(32 * (scale j : ℝ) * (lg (scale j) : ℝ)) + 1 :=
        Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    _ ≤ 81 / 8 * √(n : ℝ) * histogramGrowth ^ j + 1 := by linarith

/-- The geometric sum `∑_{j<n} 𝖦^j` is less than `201 𝖦^n`. -/
theorem sum_range_histogramGrowth_pow_lt (n : ℕ) :
    ∑ j ∈ Finset.range n, histogramGrowth ^ j < 201 * histogramGrowth ^ n := by
  have h := geom_sum_mul histogramGrowth n
  have hG1 := one_lt_histogramGrowth
  have hG201 := lt_histogramGrowth_sub_one
  have hS0 : 0 ≤ ∑ j ∈ Finset.range n, histogramGrowth ^ j :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hGn : 0 < histogramGrowth ^ n := by positivity
  nlinarith

/-- `√n ≤ 𝖦^n` for `n ≥ 10000`. -/
theorem sqrt_le_histogramGrowth_pow {n : ℕ} (hn : 10000 ≤ n) :
    √(n : ℝ) ≤ histogramGrowth ^ n := by
  have hG0 : 0 ≤ histogramGrowth := histogramGrowth_nonneg
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [← pow_mul, mul_comm, histogramGrowth_pow_two_mul]
  exact le_growthRatio_pow hn

/-- **Growth of the depth-width sums**: for every `n ≥ 10000`,
`2 ∑_{j<n} dw(b_j) + 1 < 4075 √n 𝖦^n`. -/
@[collatz_pos_dens "lem_s05_width_sum_bound"]
theorem two_mul_sum_dw_scale_add_one_lt {n : ℕ} (hn : 10000 ≤ n) :
    2 * ∑ j ∈ Finset.range n, (dw (scale j) : ℝ) + 1 <
      4075 * √(n : ℝ) * histogramGrowth ^ n := by
  set G := histogramGrowth with hGdef
  have hG1 : 1 < G := one_lt_histogramGrowth
  have hsq0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hsq1 : 1 ≤ √(n : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ n))
  have hsum1 : ∑ j ∈ Finset.range n, (dw (scale j) : ℝ) <
      ∑ j ∈ Finset.range n, (81 / 8 * √(n : ℝ) * G ^ j + 1) :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega))
      fun j hj => dw_scale_lt_sqrt_mul_histogramGrowth_pow hn (Finset.mem_range.1 hj)
  have hgeom : ∑ j ∈ Finset.range n, G ^ j < 201 * G ^ n :=
    sum_range_histogramGrowth_pow_lt n
  have hsum2 : ∑ j ∈ Finset.range n, (81 / 8 * √(n : ℝ) * G ^ j + 1) =
      81 / 8 * √(n : ℝ) * ∑ j ∈ Finset.range n, G ^ j + n := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hGn : √(n : ℝ) ≤ G ^ n := sqrt_le_histogramGrowth_pow hn
  have hn_le : (n : ℝ) ≤ √(n : ℝ) * G ^ n := by
    calc (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt (by positivity)).symm
      _ ≤ √(n : ℝ) * G ^ n := mul_le_mul_of_nonneg_left hGn hsq0
  have hprod1 : 1 ≤ √(n : ℝ) * G ^ n := by
    have : 1 ≤ G ^ n := one_le_pow₀ hG1.le
    nlinarith
  have hbig : ∑ j ∈ Finset.range n, (dw (scale j) : ℝ) < 2037 * (√(n : ℝ) * G ^ n) := by
    have : 81 / 8 * √(n : ℝ) * ∑ j ∈ Finset.range n, G ^ j ≤
        81 / 8 * √(n : ℝ) * (201 * G ^ n) := by gcongr
    nlinarith
  nlinarith

end CollatzPosDens
