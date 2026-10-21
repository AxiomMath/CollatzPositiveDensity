/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhDelta
public import CollatzPosDens.FirstCrossing.PhDeltaBounds
public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.Recipe.CovGen
public import CollatzPosDens.Terminal.S06Tj
public import CollatzPosDens.Transfer.S02Log2Bstar

/-!
# The terminal majorant is small

For every integer `j ≥ J_c = 23000` the terminal majorant satisfies `T_j < 2^{-29}`.

Write `x = 2^{12} 𝗀^j`, `a = a_mx(o) = 18693/10000` and `δ = log₂ 𝗀`, so that `𝗀^y = 2^{δ y}`
and `1/70 < δ < 1/69`. Since `log 𝗀 ≤ 1/100` and `12 log 2 < 9`, `log x ≤ j/64`; moreover
`x^{-a} ≤ 2^{-22} 𝗀^{-a j}`, `x^{-2} = 2^{-24} 𝗀^{-2j}` and `B_F(o) < 2^{349}`. Hence
`T_j ≤ τ₁ + τ₂ + τ₃ + τ₄` with
`τ₁ = 2^{332} j^{11/2} 𝗀^{-(a-1/2) j}`, `τ₂ = 2^{-13} j^{9/2} 𝗀^{-3j/2}`,
`τ₃ = 2^{35} j^{9/2} 𝗀^{-11j/2}` and `τ₄ = 2^{-26} j^{9/2} 𝗀^{j/2} 2^{-j/56}`, the constants
coming from the prefactor `5` of `T_j` through `5 · 2^{329} ≤ 2^{332}`, `5 · 2^{-16} ≤ 2^{-13}`,
`5 (2^{32} + 2^{29}) ≤ 2^{35}` and `5 · 2^{-29} ≤ 2^{-26}`.
Each exponential decays at a binary rate `r_i` read off from the bounds on `δ`, and
`j ≤ 2^{j/1500}` for `j ≥ 22500`; so `τ_i ≤ 2^{c_i - γ_i j}` with `γ_i > 0` and
`c_i - 23000 γ_i < -31`. Therefore `T_j < 4 · 2^{-31} = 2^{-29}`.

## Main results

* `CollatzPosDens.growthRatio_rpow_eq_two_rpow`: `𝗀^y = 2^{δ y}`.
* `CollatzPosDens.self_le_two_rpow_div_fifteenHundred`: `y ≤ 2^{y/1500}` for real `y ≥ 22500`.
* `CollatzPosDens.terminalMajorant_lt`: `T_j < 2^{-29}` for every `j ≥ J_c`.

## Implementation notes

The inequality `y ≤ 2^{y/1500}` is proved for every real `y ≥ 22500` on the natural-logarithm
scale, from `log y = log 22500 + log (y/22500) ≤ 15 log 2 + y/22500 - 1` (as `22500 ≤ 2^{15}`),
rather than by induction on `⌊y/1500⌋`: both sides of `log y ≤ (y/1500) log 2` then agree at
`y = 22500`, and the comparison of slopes needs only `log 2 > 1/15`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.2.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- Real powers of the growth ratio in binary form: `𝗀 ^ y = 2 ^ (δ y)`. -/
theorem growthRatio_rpow_eq_two_rpow (y : ℝ) :
    (growthRatio : ℝ) ^ y = (2 : ℝ) ^ (logGrowthRate * y) := by
  rw [← rpow_logGrowthRate, ← Real.rpow_mul (by norm_num)]

/-- A linear function eventually dominates the logarithm: `y ≤ 2 ^ (y / 1500)` for real
`y ≥ 22500`. -/
theorem self_le_two_rpow_div_fifteenHundred {y : ℝ} (hy : 22500 ≤ y) :
    y ≤ (2 : ℝ) ^ (y / 1500) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hl2 := log_two_bounds.1
  have hlog : Real.log y ≤ y / 1500 * Real.log 2 := by
    have h1 : Real.log y = Real.log 22500 + Real.log (y / 22500) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      ring
    have h2 : Real.log (y / 22500) ≤ y / 22500 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 22500 ≤ 15 * Real.log 2 := by
      have h := Real.log_le_log (by norm_num) (show (22500 : ℝ) ≤ 2 ^ 15 by norm_num)
      rw [Real.log_pow] at h
      push_cast at h
      exact h
    have h4 : 0 ≤ (y - 22500) * (Real.log 2 - 1 / 15) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  calc y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
    _ ≤ Real.exp (Real.log 2 * (y / 1500)) := Real.exp_le_exp.2 (by linarith)
    _ = (2 : ℝ) ^ (y / 1500) := (Real.rpow_def_of_pos two_pos _).symm

/-- **The terminal majorant is small.** For every integer `j ≥ J_c`, `T_j < 2^{-29}`. -/
@[collatz_pos_dens "lem_s06_terminal_small"]
theorem terminalMajorant_lt {j : ℕ} (hj : covGen ≤ j) :
    terminalMajorant j < (2 : ℝ) ^ (-29 : ℝ) := by
  rw [covGen_def] at hj
  rw [terminalMajorant_def, mxProfile_o]
  set J : ℝ := (j : ℝ) with hJdef
  have hJ : (23000 : ℝ) ≤ J := by rw [hJdef]; exact_mod_cast hj
  have hJ0 : 0 < J := by linarith
  obtain ⟨hδ1, hδ2⟩ := logGrowthRate_bounds
  have hgr := growthRatio_rpow_eq_two_rpow
  set δ := logGrowthRate with hδdef
  have hg := growthRatio_cast_pos
  set g : ℝ := (growthRatio : ℝ) with hgdef
  have ha : (amix .o : ℝ) = 18693 / 10000 := amix_cast_o
  set a : ℝ := (amix .o : ℝ) with hadef
  have hJp : ∀ p : ℝ, 0 ≤ p → J ^ p ≤ (2 : ℝ) ^ (p * J / 1500) := by
    intro p hp
    calc J ^ p ≤ ((2 : ℝ) ^ (J / 1500)) ^ p :=
          Real.rpow_le_rpow hJ0.le (self_le_two_rpow_div_fifteenHundred (by linarith)) hp
      _ = (2 : ℝ) ^ (p * J / 1500) := by
          rw [← Real.rpow_mul (by norm_num)]
          congr 1
          ring
  have key : ∀ c p r : ℝ, 0 ≤ p → c + p * J / 1500 - r * J < -31 →
      (2 : ℝ) ^ c * J ^ p * (2 : ℝ) ^ (-(r * J)) < (2 : ℝ) ^ (-31 : ℝ) := by
    intro c p r hp h
    calc (2 : ℝ) ^ c * J ^ p * (2 : ℝ) ^ (-(r * J))
        ≤ (2 : ℝ) ^ c * (2 : ℝ) ^ (p * J / 1500) * (2 : ℝ) ^ (-(r * J)) := by
          gcongr
          exact hJp p hp
      _ = (2 : ℝ) ^ (c + p * J / 1500 - r * J) := by
          rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos, sub_eq_add_neg]
      _ < (2 : ℝ) ^ (-31 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
  have hdecay : ∀ c r : ℝ, 0 ≤ c → r ≤ c / 70 → g ^ (-(c * J)) ≤ (2 : ℝ) ^ (-(r * J)) := by
    intro c r hc hr
    rw [hgr]
    have h := mul_nonneg (sub_nonneg.2 hδ1.le) (mul_nonneg hc hJ0.le)
    have h' := mul_le_mul_of_nonneg_right hr hJ0.le
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hgJ : 1 ≤ g ^ J := Real.one_le_rpow one_lt_growthRatio_cast.le hJ0.le
  set x := (2 : ℝ) ^ 12 * g ^ J with hxdef
  have hlogx : Real.log x ≤ J / 64 := by
    rw [hxdef, Real.log_mul (by positivity) (by positivity), Real.log_rpow hg, Real.log_pow,
      hgdef, growthRatio_cast]
    have h1 : Real.log (101 / 100 : ℝ) ≤ 1 / 100 := by
      have := Real.log_le_sub_one_of_pos (x := 101 / 100) (by norm_num)
      linarith
    have h2 := log_two_bounds.2
    push_cast
    nlinarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by rw [hxdef]; nlinarith)
  have h2pow : (2 : ℝ) ^ 12 = (2 : ℝ) ^ (12 : ℝ) := by norm_num
  have hxa : x ^ (-a) ≤ (2 : ℝ) ^ (-22 : ℝ) * g ^ (-(a * J)) := by
    rw [hxdef, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hg.le, h2pow,
      ← Real.rpow_mul (by norm_num), show J * -a = -(a * J) by ring]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [ha]; norm_num)) (by positivity)
  have hx2 : x ^ (-2 : ℝ) = (2 : ℝ) ^ (-24 : ℝ) * g ^ (-(2 * J)) := by
    rw [hxdef, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hg.le, h2pow,
      ← Real.rpow_mul (by norm_num), show J * -2 = -(2 * J) by ring]
    norm_num
  have hB : fourierPrefactor .o < (2 : ℝ) ^ (349 : ℝ) := by
    have h := logb_two_fourierPrefactor_mem_o.2
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (fourierPrefactor_pos .o)] at h
    exact h.trans (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num))
  have hB0 := fourierPrefactor_pos .o
  have hP0 : 0 ≤ J ^ (9 / 2 : ℝ) * g ^ (J / 2) := by positivity
  have hτ1 : 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) *
      (2 * (126 * fourierPrefactor .o * x ^ (-a) * Real.log x)) < (2 : ℝ) ^ (-31 : ℝ) := by
    have hg1 : g ^ (J / 2) * g ^ (-(a * J)) = g ^ (-(13693 / 10000 * J)) := by
      rw [← Real.rpow_add hg, ha]
      congr 1
      ring
    have hc : (315 / 16 : ℝ) * ((2 : ℝ) ^ (349 : ℝ) * (2 : ℝ) ^ (-22 : ℝ)) ≤
        (2 : ℝ) ^ (332 : ℝ) := by
      rw [← Real.rpow_add two_pos, show (332 : ℝ) = 5 + (349 + -22) by norm_num,
        Real.rpow_add two_pos (5 : ℝ), show (2 : ℝ) ^ (5 : ℝ) = 32 by norm_num]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) *
          (2 * (126 * fourierPrefactor .o * x ^ (-a) * Real.log x))
        ≤ 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) *
          (2 * (126 * 2 ^ (349 : ℝ) * ((2 : ℝ) ^ (-22 : ℝ) * g ^ (-(a * J))) * (J / 64))) := by
          gcongr
      _ = (315 / 16 : ℝ) * ((2 : ℝ) ^ (349 : ℝ) * (2 : ℝ) ^ (-22 : ℝ)) * (J ^ (9 / 2 : ℝ) * J) *
            (g ^ (J / 2) * g ^ (-(a * J))) := by ring
      _ ≤ (2 : ℝ) ^ (332 : ℝ) * J ^ (11 / 2 : ℝ) * (2 : ℝ) ^ (-(13693 / 700000 * J)) := by
          rw [← Real.rpow_add_one hJ0.ne', hg1, show (9 / 2 : ℝ) + 1 = 11 / 2 by norm_num]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity))
            (hdecay _ _ (by norm_num) (by norm_num)) (by positivity) (by positivity)
      _ < (2 : ℝ) ^ (-31 : ℝ) := key _ _ _ (by norm_num) (by linarith)
  have hτ2 : 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) * (2 * (105 * x ^ (-2 : ℝ))) <
      (2 : ℝ) ^ (-31 : ℝ) := by
    have hg1 : g ^ (J / 2) * g ^ (-(2 * J)) = g ^ (-(3 / 2 * J)) := by
      rw [← Real.rpow_add hg]
      congr 1
      ring
    have hc : (1050 : ℝ) * (2 : ℝ) ^ (-24 : ℝ) ≤ (2 : ℝ) ^ (-13 : ℝ) := by
      rw [show (-13 : ℝ) = 11 + -24 by norm_num, Real.rpow_add two_pos]
      rw [show (2 : ℝ) ^ (11 : ℝ) = 2048 by norm_num]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) * (2 * (105 * x ^ (-2 : ℝ)))
        = ((1050 : ℝ) * (2 : ℝ) ^ (-24 : ℝ)) * J ^ (9 / 2 : ℝ) *
            (g ^ (J / 2) * g ^ (-(2 * J))) := by
          rw [hx2]; ring
      _ ≤ (2 : ℝ) ^ (-13 : ℝ) * J ^ (9 / 2 : ℝ) * (2 : ℝ) ^ (-(3 / 140 * J)) := by
          rw [hg1]
          gcongr
          exact hdecay _ _ (by norm_num) (by norm_num)
      _ < (2 : ℝ) ^ (-31 : ℝ) := key _ _ _ (by norm_num) (by linarith)
  have hτ3 : 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) * ((2 ^ 32 + 2 ^ 29) * g ^ (-(6 * J))) <
      (2 : ℝ) ^ (-31 : ℝ) := by
    have hg1 : g ^ (J / 2) * g ^ (-(6 * J)) = g ^ (-(11 / 2 * J)) := by
      rw [← Real.rpow_add hg]
      congr 1
      ring
    have hc : (5 * (2 ^ 32 + 2 ^ 29) : ℝ) ≤ (2 : ℝ) ^ (35 : ℝ) := by
      rw [show (35 : ℝ) = ((35 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    calc 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) * ((2 ^ 32 + 2 ^ 29) * g ^ (-(6 * J)))
        = (5 * (2 ^ 32 + 2 ^ 29) : ℝ) * J ^ (9 / 2 : ℝ) * (g ^ (J / 2) * g ^ (-(6 * J))) := by
          ring
      _ ≤ (2 : ℝ) ^ (35 : ℝ) * J ^ (9 / 2 : ℝ) * (2 : ℝ) ^ (-(11 / 140 * J)) := by
          rw [hg1]
          gcongr
          exact hdecay _ _ (by norm_num) (by norm_num)
      _ < (2 : ℝ) ^ (-31 : ℝ) := key _ _ _ (by norm_num) (by linarith)
  have hτ4 : 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) *
      ((2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-(J / 56))) < (2 : ℝ) ^ (-31 : ℝ) := by
    have hg1 : g ^ (J / 2) * (2 : ℝ) ^ (-(J / 56)) ≤ (2 : ℝ) ^ (-(41 / 3864 * J)) := by
      rw [hgr, ← Real.rpow_add two_pos]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have hc : (5 : ℝ) * (2 : ℝ) ^ (-29 : ℝ) ≤ (2 : ℝ) ^ (-26 : ℝ) := by
      rw [show (-26 : ℝ) = 3 + -29 by norm_num, Real.rpow_add two_pos,
        show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) * ((2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-(J / 56)))
        = ((5 : ℝ) * (2 : ℝ) ^ (-29 : ℝ)) * J ^ (9 / 2 : ℝ) *
            (g ^ (J / 2) * (2 : ℝ) ^ (-(J / 56))) := by ring
      _ ≤ (2 : ℝ) ^ (-26 : ℝ) * J ^ (9 / 2 : ℝ) * (2 : ℝ) ^ (-(41 / 3864 * J)) := by
          gcongr
      _ < (2 : ℝ) ^ (-31 : ℝ) := key _ _ _ (by norm_num) (by linarith)
  have h29 : (2 : ℝ) ^ (-29 : ℝ) = 4 * (2 : ℝ) ^ (-31 : ℝ) := by
    rw [show (-29 : ℝ) = 2 + -31 by norm_num, Real.rpow_add two_pos]
    norm_num
  rw [h29]
  linarith [hτ1, hτ2, hτ3, hτ4, show 5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) *
      (2 * (126 * fourierPrefactor .o * x ^ (-a) * Real.log x + 105 * x ^ (-2 : ℝ)) +
        (2 ^ 32 + 2 ^ 29) * g ^ (-(6 * J)) + (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-(J / 56))) =
      5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) *
          (2 * (126 * fourierPrefactor .o * x ^ (-a) * Real.log x)) +
        5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) * (2 * (105 * x ^ (-2 : ℝ))) +
        5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) * ((2 ^ 32 + 2 ^ 29) * g ^ (-(6 * J))) +
        5 * J ^ (9 / 2 : ℝ) * g ^ (J / 2) * ((2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-(J / 56))) by ring]

end CollatzPosDens
