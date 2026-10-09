/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.FirstCrossing.PhDelta
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.FirstCrossing.ScalesUpper
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The conductor is below the real endpoint

The conductor `q_* = k_{N_*} + ∑_{j<N_*} h_{b_j}` satisfies
$$\log_2 q_* + 1 < 16 + N_*\delta.$$

Since the scales grow by a factor at least `𝗀 = 101/100` per step, `∑_{j<N} b_j < 100 b_N`.
With `h_b ≤ 8b/5` and `k_N ≤ b_N/4` this gives `20 (k_N + ∑_{j<N} h_{b_j}) < 3205 b_N`, and
`b_N < 201 𝗀^N` then yields `k_N + ∑_{j<N} h_{b_j} < 2^{15} 𝗀^N = 2^{15 + Nδ}` for every `N`.
Taking `log₂` at `N = N_*` gives the claim.

## Main results

* `CollatzPosDens.sum_scale_lt_hundred_mul_scale`: `∑_{j<N} b_j < 100 b_N`.
* `CollatzPosDens.conductorAt_lt_two_pow_mul_growthRatio_pow`:
  `k_N + ∑_{j<N} h_{b_j} < 2^{15} 𝗀^N` for every `N`.
* `CollatzPosDens.logb_conductor_add_one_lt`: `log₂ q_* + 1 < 16 + N_* δ`.

## Implementation notes

The bound on `conductorAt N` holds for every `N`, so the value `N_* = 9766262` is not needed;
in particular the hypothesis `N_* ≥ 1` is not used.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The scales below `N` sum to less than `100 b_N`: `∑_{j<N} b_j < 100 b_N`. -/
theorem sum_scale_lt_hundred_mul_scale (N : ℕ) :
    ∑ j ∈ range N, (scale j : ℝ) < 100 * scale N := by
  induction N with
  | zero =>
    have := nine_le_scale 0
    simp only [range_zero, sum_empty]
    have : (9 : ℝ) ≤ scale 0 := by exact_mod_cast this
    linarith
  | succ N ih =>
    rw [sum_range_succ]
    have h := scale_succ_ge_growthRatio_mul N
    rw [growthRatio_cast] at h
    linarith

/-- For every `N`, `k_N + ∑_{j<N} h_{b_j} < 2^{15} 𝗀^N`. -/
theorem conductorAt_lt_two_pow_mul_growthRatio_pow (N : ℕ) :
    (conductorAt N : ℝ) < 2 ^ 15 * (growthRatio : ℝ) ^ N := by
  have hsum := sum_scale_lt_hundred_mul_scale N
  have hup := scale_lt_mul_growthRatio_pow N
  have hk : 4 * (level N : ℝ) ≤ scale N := by exact_mod_cast four_mul_level_le N
  have hh : 5 * (∑ j ∈ range N, (hb (scale j) : ℝ)) ≤ 8 * ∑ j ∈ range N, (scale j : ℝ) := by
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun j _ => ?_
    have : 5 * hb (scale j) ≤ 8 * scale j := by rw [hb_eq]; omega
    exact_mod_cast this
  rw [conductorAt_def]
  push_cast
  linarith

/-- The conductor `q_*` satisfies `log₂ q_* + 1 < 16 + N_* δ`. -/
@[collatz_pos_dens "lem_ph_conductor"]
theorem logb_conductor_add_one_lt :
    Real.logb 2 conductor + 1 < 16 + generationThreshold * logGrowthRate := by
  have hq : (0 : ℝ) < conductor := by exact_mod_cast conductor_pos
  have hlt : Real.logb 2 conductor < 15 + generationThreshold * logGrowthRate := by
    have h2 : (2 : ℝ) ^ (15 + generationThreshold * logGrowthRate) =
        2 ^ 15 * (growthRatio : ℝ) ^ generationThreshold := by
      rw [Real.rpow_add (by norm_num), mul_comm (generationThreshold : ℝ),
        Real.rpow_mul_natCast (by norm_num), rpow_logGrowthRate]
      norm_num
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) hq, h2]
    exact conductorAt_lt_two_pow_mul_growthRatio_pow generationThreshold
  linarith

end CollatzPosDens
