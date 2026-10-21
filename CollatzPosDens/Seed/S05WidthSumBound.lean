/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesUpper
public import CollatzPosDens.FirstCrossing.Width
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.S04Clog
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Growth of the width sums

For every integer `n ≥ generationThreshold = 9853`,
$$2 \sum_{j < n} \mathrm{wd}(b_j) + 1 < 37170 \sqrt n\, \mathsf g^{n/2},$$
where `b_j` are the scales, `wd` is the width and `𝗀 = 101/100` is the growth ratio.

The proof combines `wd(b) ≤ ⌈√(32 b lg b)⌉` with the upper growth `b_j < 16644 𝗀^j` of the
scales. Since `16644 < 2^15` and `𝗀^{69} < 2`, one gets `lg(b_j) ≤ 16 + j/69`, so for `j < n`
and `n ≥ 9853`, `lg(b_j) ≤ n/62` (as `16 · 62 · 69 = 68448 ≤ 7 · 9853`), and
`32 · 16644 · 10^4 ≤ 62 · 9269^2` gives `wd(b_j) < (9269/100) √n 𝗀^{j/2} + 1`. Summing the
geometric series with `𝗀^{1/2} - 1 > 2/401` (as `(403/401)^2 < 𝗀`) gives
`2 ∑_{j<n} wd(b_j) + 1 < (3716869/100) √n 𝗀^{n/2} + 2n + 1`. Finally `𝗀^n ≥ 49 n`, so
`2n + 1 ≤ 3n ≤ (3/7) √n 𝗀^{n/2}`, and `3716869/100 + 3/7 = 26018383/700 ≤ 37170`.

## Main results

* `CollatzPosDens.lg_scale_le`: `lg(b_j) ≤ 16 + j/69`.
* `CollatzPosDens.two_mul_sum_wd_scale_add_one_lt`: the bound on `2 ∑_{j<n} wd(b_j) + 1`.

## Implementation notes

The inequality is stated in `ℝ`, with the natural-number widths cast to `ℝ` and `𝗀^{n/2}` a
real power. In the proof it is handled as the `n`-th power of `√𝗀`. The bound `𝗀^n ≥ 49 n` is
obtained from `𝗀^{5k} ≥ (1 + k/100)^5 ≥ (k/100)^5` with `k = ⌊n/5⌋ ≥ 1970` (Bernoulli's
inequality) rather than from the quartic binomial term `𝗀^n ≥ \binom n4 100^{-4}`.

## References

* [Mazur, *Collatz positive density*, §17.4]
-/

@[expose] public section

namespace CollatzPosDens

/-- `lg(b_j) ≤ 16 + j/69`: the binary ceiling-logarithm of the scales grows at most like
`j/69`, since `b_j < 16644 𝗀^j`, `16644 < 2^15` and `𝗀^{69} < 2`. -/
theorem lg_scale_le (j : ℕ) :
    (lg (scale j) : ℝ) ≤ 16 + (j : ℝ) / 69 := by
  set k := j / 69 with hk
  have hjk : j < 69 * (k + 1) := by omega
  have hg1 : (1 : ℝ) ≤ (growthRatio : ℝ) := one_lt_growthRatio_cast.le
  have h69 : (growthRatio : ℝ) ^ 69 < 2 := by rw [growthRatio_cast]; norm_num
  have hlt : (scale j : ℝ) < (2 : ℝ) ^ (k + 16) := by
    calc (scale j : ℝ) < 16644 * (growthRatio : ℝ) ^ j := scale_lt_mul_growthRatio_pow j
      _ ≤ 16644 * (growthRatio : ℝ) ^ (69 * (k + 1)) := by
          gcongr 16644 * ?_
          exact pow_le_pow_right₀ hg1 hjk.le
      _ = 16644 * ((growthRatio : ℝ) ^ 69) ^ (k + 1) := by rw [pow_mul]
      _ ≤ 16644 * 2 ^ (k + 1) := by gcongr
      _ < 2 ^ 15 * 2 ^ (k + 1) := by gcongr; norm_num
      _ = 2 ^ (k + 16) := by rw [← pow_add]; ring_nf
  have hle : lg (scale j) ≤ k + 16 :=
    lg_le_of_le_two_pow (by exact_mod_cast hlt.le)
  have hkj : (k : ℝ) ≤ (j : ℝ) / 69 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : k * 69 ≤ j)
  have : (lg (scale j) : ℝ) ≤ k + 16 := by exact_mod_cast hle
  linarith

/-- `49 n ≤ 𝗀^n` for `n ≥ 9853`, from `𝗀^{5k} ≥ (k/100)^5` with `k = ⌊n/5⌋ ≥ 1970`. -/
private theorem forty_nine_mul_le_growthRatio_pow {n : ℕ} (hn : 9853 ≤ n) :
    49 * (n : ℝ) ≤ (growthRatio : ℝ) ^ n := by
  set k := n / 5 with hk
  have hnk : n ≤ 5 * k + 4 := by omega
  have hk0 : 1970 ≤ k := by omega
  have hg1 : (1 : ℝ) ≤ (growthRatio : ℝ) := one_lt_growthRatio_cast.le
  have hb : 1 + (k : ℝ) * (1 / 100) ≤ (growthRatio : ℝ) ^ k := by
    rw [growthRatio_cast, show (101 / 100 : ℝ) = 1 + 1 / 100 by norm_num]
    exact one_add_mul_le_pow (by norm_num) k
  have hkR : (1970 : ℝ) ≤ k := by exact_mod_cast hk0
  have hnR : (n : ℝ) ≤ 5 * k + 4 := by exact_mod_cast hnk
  have hk4 : (1970 : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 := by gcongr
  have hk5 : (k : ℝ) * 1970 ^ 4 ≤ (k : ℝ) ^ 5 := by
    rw [show (k : ℝ) ^ 5 = k * k ^ 4 by ring]
    exact mul_le_mul_of_nonneg_left hk4 (by positivity)
  have hk5' : 49 * (n : ℝ) ≤ ((k : ℝ) / 100) ^ 5 := by
    rw [div_pow]; norm_num; nlinarith
  calc 49 * (n : ℝ) ≤ ((k : ℝ) / 100) ^ 5 := hk5'
    _ ≤ (1 + (k : ℝ) * (1 / 100)) ^ 5 := by gcongr; linarith
    _ ≤ ((growthRatio : ℝ) ^ k) ^ 5 := by gcongr
    _ = (growthRatio : ℝ) ^ (5 * k) := by rw [← pow_mul, mul_comm]
    _ ≤ (growthRatio : ℝ) ^ n := pow_le_pow_right₀ hg1 (by omega)

/-- For every `n ≥ generationThreshold = 9853`, `2 ∑_{j<n} wd(b_j) + 1 < 37170 √n 𝗀^{n/2}`,
where `b_j = scale j`. -/
@[collatz_pos_dens "lem_s05_width_sum_bound"]
theorem two_mul_sum_wd_scale_add_one_lt {n : ℕ} (hn : generationThreshold ≤ n) :
    2 * ∑ j ∈ Finset.range n, (wd (scale j) : ℝ) + 1 <
      37170 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) := by
  rw [generationThreshold_def] at hn
  set G := √(growthRatio : ℝ) with hGdef
  have hgpos := growthRatio_cast_pos
  have hGsq : G ^ 2 = (growthRatio : ℝ) := Real.sq_sqrt hgpos.le
  have hGrpow : (growthRatio : ℝ) ^ ((n : ℝ) / 2) = G ^ n := by
    rw [hGdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hgpos.le]
    ring_nf
  rw [hGrpow]
  have hGpow2 : ∀ j : ℕ, G ^ (2 * j) = (growthRatio : ℝ) ^ j := fun j => by
    rw [pow_mul, hGsq]
  have hG401 : 2 / 401 < G - 1 := by
    have : (403 / 401 : ℝ) < G := by
      rw [hGdef, growthRatio_cast]
      exact Real.lt_sqrt_of_sq_lt (by norm_num)
    linarith
  have hG1 : 1 < G := by linarith
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hnR : (9853 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hsqsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hterm : ∀ j ∈ Finset.range n,
      (wd (scale j) : ℝ) < 9269 / 100 * √(n : ℝ) * G ^ j + 1 := by
    intro j hj
    have hjn : j < n := Finset.mem_range.1 hj
    have hjR : (j : ℝ) ≤ n := by exact_mod_cast hjn.le
    have hb := scale_lt_mul_growthRatio_pow j
    have hb0 : (0 : ℝ) ≤ scale j := Nat.cast_nonneg _
    have hlg := lg_scale_le j
    have hlg0 : (0 : ℝ) ≤ lg (scale j) := Nat.cast_nonneg _
    have hlgn : (lg (scale j) : ℝ) ≤ n / 62 := by linarith
    have hgj : (growthRatio : ℝ) ^ j = (G ^ j) ^ 2 := by
      rw [← pow_mul, mul_comm, hGpow2]
    have hgj0 : (0 : ℝ) ≤ (growthRatio : ℝ) ^ j := by positivity
    have hroot : √(32 * (scale j : ℝ) * (lg (scale j) : ℝ)) ≤
        9269 / 100 * √(n : ℝ) * G ^ j := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have e : (9269 / 100 * √(n : ℝ) * G ^ j) ^ 2 =
          (9269 / 100) ^ 2 * n * (growthRatio : ℝ) ^ j := by
        rw [hgj, mul_pow, mul_pow, hsqsq]
      rw [e]
      have hng : (0 : ℝ) ≤ n * (growthRatio : ℝ) ^ j := by positivity
      calc 32 * (scale j : ℝ) * (lg (scale j) : ℝ)
          ≤ 32 * (16644 * (growthRatio : ℝ) ^ j) * (n / 62) := by gcongr
        _ ≤ (9269 / 100) ^ 2 * n * (growthRatio : ℝ) ^ j := by nlinarith
    calc (wd (scale j) : ℝ) ≤ (⌈√(32 * (scale j : ℝ) * (lg (scale j) : ℝ))⌉₊ : ℝ) := by
          exact_mod_cast wd_le_sqrt_ceil (scale j)
      _ < √(32 * (scale j : ℝ) * (lg (scale j) : ℝ)) + 1 :=
          Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
      _ ≤ 9269 / 100 * √(n : ℝ) * G ^ j + 1 := by linarith
  have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.2 (by omega)
  have hsum1 : ∑ j ∈ Finset.range n, (wd (scale j) : ℝ) <
      ∑ j ∈ Finset.range n, (9269 / 100 * √(n : ℝ) * G ^ j + 1) :=
    Finset.sum_lt_sum_of_nonempty hne hterm
  have hgeom : ∑ j ∈ Finset.range n, G ^ j < 401 / 2 * G ^ n := by
    have h := geom_sum_mul G n
    have hS0 : 0 ≤ ∑ j ∈ Finset.range n, G ^ j := Finset.sum_nonneg (fun _ _ => by positivity)
    have hGn : 0 < G ^ n := by positivity
    nlinarith
  have hsum2 : ∑ j ∈ Finset.range n, (9269 / 100 * √(n : ℝ) * G ^ j + 1) =
      9269 / 100 * √(n : ℝ) * ∑ j ∈ Finset.range n, G ^ j + n := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
  have hGn : 7 * √(n : ℝ) ≤ G ^ n := by
    have h49 := forty_nine_mul_le_growthRatio_pow hn
    have hsq : (7 * √(n : ℝ)) ^ 2 ≤ (G ^ n) ^ 2 := by
      rw [mul_pow, hsqsq, ← pow_mul, mul_comm n 2, hGpow2]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 hsq
  have hn_le : 7 * (n : ℝ) ≤ √(n : ℝ) * G ^ n := by
    calc 7 * (n : ℝ) = √(n : ℝ) * (7 * √(n : ℝ)) := by
          linear_combination (-7) * hsqsq
      _ ≤ √(n : ℝ) * G ^ n := mul_le_mul_of_nonneg_left hGn hsq0
  have hmain : 9269 / 100 * √(n : ℝ) * ∑ j ∈ Finset.range n, G ^ j ≤
      9269 / 100 * √(n : ℝ) * (401 / 2 * G ^ n) := by gcongr
  nlinarith

end CollatzPosDens
