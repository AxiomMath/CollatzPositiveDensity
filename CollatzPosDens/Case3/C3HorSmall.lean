/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The horizontal passage tail at a very far gap

For real `G ≥ 2 ^ 160` we have `2 ^ 55 * exp (-G ^ (1/5) / 65536) < (2 * G) ^ (-1/2)`.

Write `z = G ^ (1/20)`, so that `G = z ^ 20`, `G ^ (1/5) = z ^ 4` and `z ≥ 2 ^ 8`. Taking
logarithms, the claim becomes `(111/2) log 2 + 10 log z < z ^ 4 / 2 ^ 16`. Since `log 2 ≤ 1` and
`log z ≤ z - 1`, it suffices that `111/2 + 10 z < z ^ 4 / 2 ^ 16`, and indeed
`z ^ 4 / 2 ^ 16 ≥ 2 ^ 8 z = 10 z + 246 z ≥ 10 z + 246 · 2 ^ 8` for `z ≥ 2 ^ 8`.

## Main results

* `CollatzPosDens.c3HorSmall`: `2 ^ 55 * exp (-G ^ (1/5) / 65536) < (2 * G) ^ (-1/2)` for
  `G ≥ 2 ^ 160`.

## Implementation notes

The source argues with `y = G ^ (1/5)` and `y ^ (1/4)`; we use the single auxiliary quantity
`z = G ^ (1/20) = y ^ (1/4)` instead, which turns the final comparison into a polynomial
inequality in `z`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- For real `G ≥ 2 ^ 160`, `2 ^ 55 * exp (-G ^ (1/5) / 65536) < (2 * G) ^ (-1/2)`. -/
@[collatz_pos_dens "lem_c3_hor_small"]
theorem c3HorSmall {G : ℝ} (hG : (2 : ℝ) ^ 160 ≤ G) :
    (2 : ℝ) ^ 55 * Real.exp (-G ^ (1 / 5 : ℝ) / 65536) < (2 * G) ^ (-1 / 2 : ℝ) := by
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hG
  set z : ℝ := G ^ (1 / 20 : ℝ) with hz_def
  have hz0 : 0 < z := Real.rpow_pos_of_pos hG0 _
  have hzG : z ^ 20 = G := by
    rw [hz_def, ← Real.rpow_natCast, ← Real.rpow_mul hG0.le]; norm_num
  have hy : G ^ (1 / 5 : ℝ) = z ^ 4 := by
    rw [hz_def, ← Real.rpow_natCast, ← Real.rpow_mul hG0.le]; norm_num
  have hz8 : (256 : ℝ) ≤ z := by
    have h : (256 : ℝ) ^ 20 ≤ z ^ 20 := by rw [hzG]; norm_num at hG ⊢; linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hz0.le (by norm_num)).1 h
  rw [hy, Real.rpow_def_of_pos (by positivity), ← hzG]
  have h2 : (2 : ℝ) ^ 55 = Real.exp (55 * Real.log 2) := by
    rw [show (55 : ℝ) * Real.log 2 = Real.log (2 ^ 55) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [h2, ← Real.exp_add, Real.exp_lt_exp, Real.log_mul (by norm_num) (by positivity),
    Real.log_pow]
  have hl2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hlz : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz0
  have hz3 : (256 : ℝ) ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ (by norm_num) hz8 3
  push_cast
  nlinarith

end CollatzPosDens
