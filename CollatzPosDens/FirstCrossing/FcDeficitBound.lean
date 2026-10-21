/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.Recipe.S04Clog
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FcLateBound
public import CollatzPosDens.FirstCrossing.FcLateWindowDeficit
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesLateLower
public import CollatzPosDens.FirstCrossing.ScalesLinearLower
public import CollatzPosDens.FirstCrossing.Width

/-!
# Deficit of the central families

For every scale index `j ∈ ℕ`, with scale `b_j` and cap `K_j`, the central family misses little
geometric mass:
$$1-\mathbf p(\mathcal C(b_j,K_j))\le 2\exp\Bigl(-\frac{529}{10^6}(b_j-14)\Bigr)
  + 2\,b_j^{-3/2} + 2^{-(K_j+1)}.$$

Write `b = b_j`, `y = y^w_j`, `κ = 2(207/500)²/9 = 4761/125000` and `X = κ y²/(b + y)`. By
`CollatzPosDens.one_sub_geomMass_centralFamily_le_dW`, `1 - 𝐩(𝒞(b, K_j)) ≤ 2e^{-X} + 2^{-(K_j+1)}`.
Since `b ≥ 16544`, the bound `⌊3b/5⌋ - 1` of `CollatzPosDens.wd` exceeds `B = ⌊b/8⌋`, so
`y = min(A, B)` with `A = ⌈√(32 b lg b)⌉`.

* If `B ≤ A`, then `y = B ≥ (b - 7)/8`, and `72 y² ≥ (b - 14)(b + y)` (with `8y = b - 7 + t`,
  `t ≥ 0`, the difference is `(7b + 343 + (17b - 112) t + 9t²)/8`), so
  `X ≥ (κ/72)(b - 14) = (529/10⁶)(b - 14)`.
* If `A < B`, then `y ≥ A`, so `y² ≥ 32 b lg b`, and `b + y ≤ 9b/8`; hence
  `X ≥ (256κ/9) lg b ≥ (256κ/(9 log 2)) log b ≥ (3/2) log b`, using `log 2 < 347/500` and
  `b ≤ 2^{lg b}`. Thus `e^{-X} ≤ b^{-3/2}`.

The first two terms have geometric majorants along the scales:
`e^{-c(b_j - 14)} ≤ e^{-16530c} (e^{-166c})^j` with `c = 529/10⁶`, from `b_j ≥ 16544 + 166j`, and
`b_j^{-3/2} ≤ 2^{-21} (𝗀^{-3/2})^j`, from `b_j ≥ 16544 𝗀^j ≥ 2^{14} 𝗀^j`.

## Main results

* `CollatzPosDens.one_sub_geomMass_centralFamily_le_exp_add_rpow`: the deficit bound above.
* `CollatzPosDens.exp_neg_mul_scale_sub_fourteen_le`: the geometric majorant of the
  exponential term.
* `CollatzPosDens.scale_rpow_neg_three_halves_le`: the geometric majorant of the power term.

## Implementation notes

The geometric mass is `ℝ≥0∞`-valued and `1 - 𝐩` is truncated subtraction; the real bound is
embedded by `ENNReal.ofReal`. The power `b_j^{-3/2}` is the real power `Real.rpow`.

## References

* [Mazur, *Collatz positive density*], §14.6.
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- The exponential estimate of the deficit bound: for an integer `b ≥ 16544` and the
window `y = min (wd b) ⌊b/8⌋`,
`exp(-2(207y/500)²/(9(b+y))) ≤ exp(-(529/10⁶)(b - 14)) + b^{-3/2}`. -/
private theorem fcDeficitBound_exp_le {b : ℕ} (hb : 16544 ≤ b) :
    exp (-2 * (207 * ((min (wd b) (b / 8) : ℕ) : ℝ) / 500) ^ 2 /
      (9 * ((b : ℝ) + ((min (wd b) (b / 8) : ℕ) : ℝ)))) ≤
      exp (-(529 / 10 ^ 6) * ((b : ℝ) - 14)) + (b : ℝ) ^ (-(3 / 2 : ℝ)) := by
  set y : ℕ := min (wd b) (b / 8) with hy_def
  have hy8 : 8 * y ≤ b := by have : y ≤ b / 8 := min_le_right _ _; omega
  have hbR : (16544 : ℝ) ≤ b := by exact_mod_cast hb
  have hyR : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hy8R : 8 * (y : ℝ) ≤ b := by exact_mod_cast hy8
  have hden : 0 < 9 * ((b : ℝ) + y) := by positivity
  set A : ℕ := ⌈√(32 * (b : ℝ) * (lg b : ℝ))⌉₊ with hA
  have h35 : b / 8 ≤ 3 * b / 5 - 1 := by omega
  rcases le_or_gt (b / 8) A with hBA | hAB
  · -- the window is `⌊b/8⌋`
    have hyB : y = b / 8 := by
      rw [hy_def]; exact min_eq_right (le_wd_iff.2 ⟨hBA, h35⟩)
    have hb7 : b ≤ 8 * y + 7 := by omega
    have hb7R : (b : ℝ) ≤ 8 * y + 7 := by exact_mod_cast hb7
    have hexp : -2 * (207 * (y : ℝ) / 500) ^ 2 / (9 * ((b : ℝ) + y)) ≤
        -(529 / 10 ^ 6) * ((b : ℝ) - 14) := by
      rw [div_le_iff₀ hden]
      set t : ℝ := 8 * y - (b - 7) with ht
      have ht0 : 0 ≤ t := by rw [ht]; linarith
      have hkey : ((b : ℝ) - 14) * (b + y) ≤ 72 * (y : ℝ) ^ 2 := by
        have hy' : (y : ℝ) = (b - 7 + t) / 8 := by rw [ht]; ring
        rw [hy']
        nlinarith [mul_nonneg ht0 (show (0 : ℝ) ≤ 17 * b - 112 by linarith), sq_nonneg t]
      nlinarith
    have := (exp_le_exp.2 hexp)
    have : 0 ≤ (b : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
    linarith
  · -- the window is `⌈√(32 b lg b)⌉`
    have hAy : A ≤ y := by
      rw [hy_def]
      exact le_min (le_wd_iff.2 ⟨le_rfl, by omega⟩) hAB.le
    have hb0 : (0 : ℝ) < b := by linarith
    have hL0 : (0 : ℝ) ≤ lg b := Nat.cast_nonneg _
    have hsq : 32 * (b : ℝ) * lg b ≤ (y : ℝ) ^ 2 := by
      have hAyR : ((A : ℕ) : ℝ) ≤ y := by exact_mod_cast hAy
      have h1 : √(32 * (b : ℝ) * (lg b : ℝ)) ≤ y := (Nat.le_ceil _).trans hAyR
      have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 32 * b * lg b by positivity)
      nlinarith [Real.sqrt_nonneg (32 * (b : ℝ) * (lg b : ℝ))]
    have hlog : log (b : ℝ) ≤ lg b * log 2 := by
      have h := Real.log_le_log hb0 (show (b : ℝ) ≤ 2 ^ lg b by exact_mod_cast le_two_pow_lg b)
      rwa [Real.log_pow] at h
    have hlog2 := log_two_bounds.2
    have hlogb0 : 0 ≤ log (b : ℝ) := Real.log_nonneg (by linarith)
    have hlogL : log (b : ℝ) ≤ 347 / 500 * lg b := by nlinarith [log_two_bounds.1]
    have hexp : -2 * (207 * (y : ℝ) / 500) ^ 2 / (9 * ((b : ℝ) + y)) ≤
        log (b : ℝ) * (-(3 / 2 : ℝ)) := by
      rw [div_le_iff₀ hden]
      have h1 : log (b : ℝ) * (9 * ((b : ℝ) + y)) ≤ 347 / 500 * lg b * (81 / 8 * b) := by
        have : 9 * ((b : ℝ) + y) ≤ 81 / 8 * b := by linarith
        exact mul_le_mul hlogL this hden.le (by positivity)
      nlinarith
    have := exp_le_exp.2 hexp
    rw [← Real.rpow_def_of_pos hb0] at this
    have : 0 ≤ exp (-(529 / 10 ^ 6) * ((b : ℝ) - 14)) := (exp_pos _).le
    linarith

/-- **Deficit of the central families**. For every `j ∈ ℕ`,
`1 - 𝐩(𝒞(b_j, K_j)) ≤ 2 exp(-(529/10⁶)(b_j - 14)) + 2 b_j^{-3/2} + 2^{-(K_j+1)}`. -/
@[collatz_pos_dens "lem_fc_deficit_bound"]
theorem one_sub_geomMass_centralFamily_le_exp_add_rpow (j : ℕ) :
    1 - geomMass (centralFamily (scale j) (cap j)) ≤
      ENNReal.ofReal (2 * exp (-(529 / 10 ^ 6) * ((scale j : ℝ) - 14)) +
        2 * (scale j : ℝ) ^ (-(3 / 2 : ℝ)) + (2 : ℝ) ^ (-((cap j : ℤ) + 1))) := by
  refine (one_sub_geomMass_centralFamily_le_dW j).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [dW_eq, two_zpow_neg_cap_add_one]
  have := fcDeficitBound_exp_le (sixteen544_le_scale j)
  linarith

/-- The geometric majorant of the exponential term along the scales: with `c = 529/10⁶`,
`exp(-c(b_j - 14)) ≤ exp(-16530c) · exp(-166c)^j`, since `b_j ≥ 16544 + 166j`. -/
theorem exp_neg_mul_scale_sub_fourteen_le (j : ℕ) :
    exp (-(529 / 10 ^ 6) * ((scale j : ℝ) - 14)) ≤
      exp (-(529 / 10 ^ 6) * 16530) * exp (-(529 / 10 ^ 6) * 166) ^ j := by
  rw [← exp_nat_mul, ← exp_add]
  apply exp_le_exp.2
  have h : ((16544 + 166 * j : ℕ) : ℝ) ≤ scale j := by exact_mod_cast scale_linear_lower j
  push_cast at h
  linarith

/-- The geometric majorant of the power term along the scales:
`b_j^{-3/2} ≤ 2^{-21} (𝗀^{-3/2})^j`, since `b_j ≥ 16544 𝗀^j ≥ 2^{14} 𝗀^j`. -/
theorem scale_rpow_neg_three_halves_le (j : ℕ) :
    (scale j : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      (1 / 2097152 : ℝ) * ((growthRatio : ℝ) ^ (-(3 / 2 : ℝ))) ^ j := by
  have hg := growthRatio_cast_pos
  have hlow : (2 : ℝ) ^ (14 : ℕ) * (growthRatio : ℝ) ^ j ≤ scale j := by
    have := scale_late_lower j
    have : (0 : ℝ) ≤ (growthRatio : ℝ) ^ j := by positivity
    norm_num; nlinarith
  calc (scale j : ℝ) ^ (-(3 / 2 : ℝ))
      ≤ ((2 : ℝ) ^ (14 : ℕ) * (growthRatio : ℝ) ^ j) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by norm_num)
    _ = ((2 : ℝ) ^ (14 : ℕ)) ^ (-(3 / 2 : ℝ)) * ((growthRatio : ℝ) ^ (-(3 / 2 : ℝ))) ^ j := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast _ j,
          ← Real.rpow_mul hg.le, ← Real.rpow_natCast ((growthRatio : ℝ) ^ (-(3 / 2 : ℝ))) j,
          ← Real.rpow_mul hg.le, mul_comm (j : ℝ)]
    _ = (1 / 2097152 : ℝ) * ((growthRatio : ℝ) ^ (-(3 / 2 : ℝ))) ^ j := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          show ((14 : ℕ) : ℝ) * (-(3 / 2 : ℝ)) = ((-21 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num

end CollatzPosDens
