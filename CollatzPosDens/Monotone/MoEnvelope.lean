/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Monotone.MoRate
public import CollatzPosDens.Monotone.MoEnvelopeHalf
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exponential envelope for the case-one rate

For a real `A ≥ 0` and integers `m ≥ 2`, `r ≥ 1`,
`max(m - r, 1)^{-A} ≤ m^{-A} exp(rt_A(m) r)`, where `rt_A(m) = 4A(1 + log m)/m` is the
case-one rate. The proof splits into two cases. If `2r ≤ m`, then `max(m - r, 1) = m - r`,
the lower-half envelope gives `(m - r)^{-A} ≤ m^{-A} e^{2Ar/m}`, and
`2A/m ≤ 4A(1 + log m)/m = rt_A(m)`. If `2r > m`, then `max(m - r, 1)^{-A} ≤ 1 = m^{-A} e^{A log m}`
and `A log m ≤ A(1 + log m) · 4r/m = rt_A(m) r` since `4r/m > 2 ≥ 1`.

## Main results

* `CollatzPosDens.max_sub_one_rpow_neg_le_mul_exp_moRate`: the envelope bound.

## Implementation notes

The bound holds for `m ≥ 1` and every `r ∈ ℕ`, which is how it is stated here. Since `m - r` is
truncated subtraction on `ℕ`, the natural number `max (m - r) 1` agrees with the integer
`max(m - r, 1)` for all `m, r`. The power `x^{-A}` with real exponent is `Real.rpow`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Envelope bound.** For real `A ≥ 0`, `m ≥ 1` and `r ∈ ℕ`,
`max(m - r, 1)^{-A} ≤ m^{-A} exp(rt_A(m) r)`. -/
@[collatz_pos_dens "lem_mo_envelope"]
theorem max_sub_one_rpow_neg_le_mul_exp_moRate {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 1 ≤ m)
    (r : ℕ) :
    ((max (m - r) 1 : ℕ) : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) * Real.exp (moRate A m * r) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hr0 : (0 : ℝ) ≤ r := by positivity
  rcases le_or_gt (2 * r) m with h | h
  · have hrm : r ≤ m := by omega
    have hM : ((max (m - r) 1 : ℕ) : ℝ) = (m : ℝ) - r := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simpa using hm
      · rw [max_eq_left (by omega), Nat.cast_sub hrm]
    rw [hM]
    refine (sub_rpow_neg_le_mul_exp_of_two_mul_le hA hm h).trans ?_
    have hrate : 2 * A * r / m ≤ moRate A m * r := by
      rw [moRate, div_mul_eq_mul_div]
      exact (div_le_div_iff_of_pos_right hm0).mpr
        (by nlinarith [mul_nonneg (mul_nonneg hA hr0) hlog, mul_nonneg hA hr0])
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (by positivity)
  · have hM : (1 : ℝ) ≤ ((max (m - r) 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h2 : (m : ℝ) < 2 * r := by exact_mod_cast h
    have hmA : (m : ℝ) ^ (-A) * Real.exp (A * Real.log m) = 1 := by
      rw [show A * Real.log m = Real.log m * A by ring, ← Real.rpow_def_of_pos hm0,
        ← Real.rpow_add hm0, neg_add_cancel, Real.rpow_zero]
    calc ((max (m - r) 1 : ℕ) : ℝ) ^ (-A) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
      _ = (m : ℝ) ^ (-A) * Real.exp (A * Real.log m) := hmA.symm
      _ ≤ _ := by
        have hrate : A * Real.log m ≤ moRate A m * r := by
          rw [moRate, div_mul_eq_mul_div, le_div_iff₀ hm0]
          nlinarith [mul_nonneg hA hlog, mul_nonneg hA hr0, mul_nonneg (mul_nonneg hA hr0) hlog]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (by positivity)

end CollatzPosDens
