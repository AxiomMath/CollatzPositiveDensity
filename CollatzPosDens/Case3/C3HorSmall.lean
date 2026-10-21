/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The horizontal passage tail at a very far gap

For real `G ≥ 2 ^ 32` we have `6 * exp (-G / 8192) < (2 * G) ^ (-1/2)`.

Both sides are positive, and after squaring the claim reads `72 G < exp (G / 4096)`. The
partial sums of the exponential series bound the right side from below: `exp t ≥ 1 + t` for
`t ≥ 0` gives `exp 1 ≥ 2`, hence `exp 32 ≥ 2 ^ 32`, and
`exp (G / 4096 - 32) ≥ 1 + (G / 4096 - 32) ≥ G / 8192` as `G / 8192 ≥ 2 ^ 19 ≥ 32`. Hence
`exp (G / 4096) ≥ 2 ^ 32 G / 8192 = 2 ^ 19 G > 72 G`.

## Main results

* `CollatzPosDens.c3HorSmall`: `6 * exp (-G / 8192) < (2 * G) ^ (-1/2)` for `G ≥ 2 ^ 32`.

## Implementation notes

The argument in [mazur2026] uses `x = G / 8192` and the bound `exp x ≥ exp (2 ^ 19) > 2 ^ 20`;
here the large exponential is split off at `32` instead, so that only `exp 1 ≥ 2` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For real `G ≥ 2 ^ 32`, `6 * exp (-G / 8192) < (2 * G) ^ (-1/2)`. -/
@[collatz_pos_dens "lem_c3_hor_small"]
theorem c3HorSmall {G : ℝ} (hG : (2 : ℝ) ^ 32 ≤ G) :
    6 * Real.exp (-G / 8192) < (2 * G) ^ (-1 / 2 : ℝ) := by
  have hG0 : 0 < G := (by positivity : (0 : ℝ) < 2 ^ 32).trans_le hG
  -- `exp t ≥ 1 + t` for `t ≥ 0`, from the partial sums of the exponential series.
  have hlin : ∀ t : ℝ, 0 ≤ t → 1 + t ≤ Real.exp t := fun t ht => by
    simpa [Finset.sum_range_succ] using Real.sum_le_exp_of_nonneg ht 2
  have h32 : (2 : ℝ) ^ 32 ≤ Real.exp 32 := by
    have : Real.exp 32 = Real.exp 1 ^ 32 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [hlin 1 zero_le_one]) 32
  -- The squared claim: `72 * G < exp (G / 4096)`.
  have key : 72 * G < Real.exp (G / 4096) := by
    have ht : 0 ≤ G / 4096 - 32 := by
      rw [sub_nonneg, le_div_iff₀ (by positivity)]; norm_num at hG ⊢; linarith
    have hsplit : Real.exp (G / 4096) = Real.exp 32 * Real.exp (G / 4096 - 32) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have h1 := hlin _ ht
    have hpos : 0 ≤ 1 + (G / 4096 - 32) := by linarith
    calc 72 * G < 2 ^ 32 * (1 + (G / 4096 - 32)) := by
          norm_num at hG ⊢; nlinarith
      _ ≤ Real.exp 32 * (1 + (G / 4096 - 32)) := mul_le_mul_of_nonneg_right h32 hpos
      _ ≤ Real.exp 32 * Real.exp (G / 4096 - 32) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hR : 0 < (2 * G) ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  refine (pow_lt_pow_iff_left₀ (by positivity) hR.le (two_ne_zero)).1 ?_
  have hR2 : ((2 * G) ^ (-1 / 2 : ℝ)) ^ 2 = (2 * G)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_neg_one]
  have hL2 : (6 * Real.exp (-G / 8192)) ^ 2 = 36 * (Real.exp (G / 4096))⁻¹ := by
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
    ring_nf
  rw [hR2, hL2, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _), inv_mul_eq_div,
    lt_div_iff₀ (by positivity)]
  linarith

end CollatzPosDens
