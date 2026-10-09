/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The quartic Taylor upper bound for the cosine

For every real `x`, `cos x ≤ 1 - x² / 2 + x⁴ / 24`.

## Main results

* `CollatzPosDens.cos_le_one_sub_sq_div_two_add_pow_four_div`: the bound
  `cos x ≤ 1 - x² / 2 + x⁴ / 24` for all real `x`.

## Implementation notes

Rather than integrating the cubic lower bound `sin x ≥ x - x³ / 6` on `[0, ∞)`, the proof
uses the half-angle formula `cos x = 1 - 2 sin² (x / 2)`, which reduces the claim to
`sin² y ≥ y² - y⁴ / 3` for `y = x / 2`. From `|y - sin y| ≤ |y|³ / 6`
(`Real.abs_sub_sin_le`) we get `|sin y| ≥ |y| - |y|³ / 6`; when the right side is nonnegative,
squaring gives `sin² y ≥ y² - y⁴ / 3 + y⁶ / 36`, and otherwise `y² > 6`, so
`y² - y⁴ / 3 = y² (1 - y² / 3) < 0 ≤ sin² y`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The quartic Taylor upper bound for the cosine: `cos x ≤ 1 - x² / 2 + x⁴ / 24` for every
real `x`. -/
@[collatz_pos_dens "lem_ch_cos_quartic"]
theorem cos_le_one_sub_sq_div_two_add_pow_four_div (x : ℝ) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  set y := x / 2 with hy
  have hx : x = 2 * y := by rw [hy]; ring
  have hc : Real.cos x = 1 - 2 * Real.sin y ^ 2 := by
    rw [hx, Real.cos_two_mul, Real.cos_sq']; ring
  have h1 := Real.abs_sub_sin_le y
  have h2 : |y| - |y| ^ 3 / 6 ≤ |Real.sin y| := by
    have := abs_sub_abs_le_abs_sub y (Real.sin y)
    linarith
  have hs : Real.sin y ^ 2 = |Real.sin y| ^ 2 := (sq_abs _).symm
  have ha : y ^ 2 = |y| ^ 2 := (sq_abs _).symm
  have key : y ^ 2 - y ^ 4 / 3 ≤ Real.sin y ^ 2 := by
    rw [hs, show y ^ 4 = (|y| ^ 2) ^ 2 by rw [← ha]; ring, ha]
    have h0 := abs_nonneg y
    have h3 := abs_nonneg (Real.sin y)
    rcases le_total 0 (|y| - |y| ^ 3 / 6) with h | h
    · nlinarith [mul_le_mul h2 h2 h h3, sq_nonneg (|y| ^ 3)]
    · nlinarith [sq_nonneg (|y|), sq_nonneg (|y| ^ 2 - 3)]
  rw [hc, hx]
  nlinarith [key]

end CollatzPosDens
