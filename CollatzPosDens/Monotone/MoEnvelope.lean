/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Monotone.MoRate
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# An exponential envelope for `moRate`

For a real `A ≥ 0` and natural numbers `m ≥ 1`, `r`,
`max(m - r, 1)^{-A} ≤ m^{-A} exp(rt_A(m) r)`, where `rt_A(m) = 4A(1 + log m)/m` is
`CollatzPosDens.moRate A m`. The proof reduces to the multiplicative form
`m ≤ max(m - r, 1) · exp(4(1 + log m) r / m)`, splitting into `2r ≤ m`, where
`(1 - x)^{-1} ≤ 1 + 2x ≤ e^{2x}` for `x = r/m ∈ [0, 1/2]`, and `2r > m`, where
`m = e^{log m}` and `log m ≤ 4(1 + log m) r / m`; the general case follows by raising both
sides to the real power `A ≥ 0`.

## Main results

* `CollatzPosDens.max_sub_one_rpow_neg_le_mul_exp_moRate`: the envelope bound.

## Implementation notes

The source assumes `m ≥ 2` and `r ≥ 1`; the bound holds for `m ≥ 1` and every `r ∈ ℕ`,
which is how it is stated here. Since `m - r` is truncated subtraction on `ℕ`, the natural
number `max (m - r) 1` agrees with the integer `max(m - r, 1)` for all `m, r`. The power
`x^{-A}` with real exponent is `Real.rpow`.

## References

* [Mazur, *Collatz positive density*], §8.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The case `A = 1` of the envelope bound, in multiplicative form:
`m ≤ max(m - r, 1) · exp(4(1 + log m) r / m)` for `m ≥ 1`. -/
private theorem natCast_le_max_sub_mul_exp (m r : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ≤ ((max (m - r) 1 : ℕ) : ℝ) * Real.exp (4 * (1 + Real.log m) / m * r) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm'
  have hr0 : (0 : ℝ) ≤ r := by positivity
  rcases le_or_gt (2 * r) m with h | h
  · have hrm : r ≤ m := by omega
    have hM : ((max (m - r) 1 : ℕ) : ℝ) = (m : ℝ) - r := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simpa using hm
      · rw [max_eq_left (by omega), Nat.cast_sub hrm]
    rw [hM]
    have h2 : (2 * r : ℝ) ≤ m := by exact_mod_cast h
    have hexp : 1 + 2 * r / m ≤ Real.exp (4 * (1 + Real.log m) / m * r) := by
      refine le_trans ?_ (Real.add_one_le_exp _)
      rw [add_comm, div_mul_eq_mul_div]
      gcongr ?_ / _ + 1
      nlinarith
    calc (m : ℝ) ≤ m + r * (m - 2 * r) / m := le_add_of_nonneg_right <|
          div_nonneg (by nlinarith) hm0.le
      _ = (m - r) * (1 + 2 * r / m) := by
          field_simp
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by linarith)
  · have hM : (1 : ℝ) ≤ ((max (m - r) 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h2 : (m : ℝ) < 2 * r := by exact_mod_cast h
    calc (m : ℝ) = Real.exp (Real.log m) := (Real.exp_log hm0).symm
      _ ≤ Real.exp (4 * (1 + Real.log m) / m * r) := by
        gcongr
        rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
        nlinarith
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le hM

/-- **Envelope bound.** For real `A ≥ 0`, `m ≥ 1` and `r ∈ ℕ`,
`max(m - r, 1)^{-A} ≤ m^{-A} exp(rt_A(m) r)`. -/
@[collatz_pos_dens "lem_mo_envelope"]
theorem max_sub_one_rpow_neg_le_mul_exp_moRate {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 1 ≤ m)
    (r : ℕ) :
    ((max (m - r) 1 : ℕ) : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) * Real.exp (moRate A m * r) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < ((max (m - r) 1 : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_pos (le_max_right _ _)
  set B := 4 * (1 + Real.log m) / m * r with hB
  have hE : Real.exp (moRate A m * r) = Real.exp B ^ A := by
    rw [← Real.exp_mul, moRate, hB]
    congr 1
    ring
  have key : (m : ℝ) ^ A ≤ ((max (m - r) 1 : ℕ) : ℝ) ^ A * Real.exp B ^ A := by
    rw [← Real.mul_rpow hM0.le (Real.exp_pos _).le]
    exact Real.rpow_le_rpow hm0.le (natCast_le_max_sub_mul_exp m r hm) hA
  have hmA : 0 < (m : ℝ) ^ A := Real.rpow_pos_of_pos hm0 A
  have hMA : 0 < ((max (m - r) 1 : ℕ) : ℝ) ^ A := Real.rpow_pos_of_pos hM0 A
  rw [Real.rpow_neg hM0.le, Real.rpow_neg hm0.le, hE, ← div_eq_inv_mul,
    le_div_iff₀ hmA, inv_mul_eq_div, div_le_iff₀ hMA, mul_comm (Real.exp B ^ A)]
  exact key

end CollatzPosDens
