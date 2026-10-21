/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exponential envelope on the lower half

For a real `A ≥ 0`, an integer `m ≥ 1` and `r ∈ ℕ` with `2r ≤ m`,
`(m - r)^{-A} ≤ m^{-A} e^{2Ar/m}`.

Writing `x = r/m ∈ [0, 1/2]`, one has `(1 - x)(1 + 2x) = 1 + x(1 - 2x) ≥ 1`, so
`(1 - x)^{-1} ≤ 1 + 2x ≤ e^{2x}`; hence `m ≤ (m - r) e^{2r/m}`, and raising both sides to the
real power `A ≥ 0` gives the bound.

## Main results

* `CollatzPosDens.sub_rpow_neg_le_mul_exp_of_two_mul_le`: the envelope bound on `2r ≤ m`.

## Implementation notes

The difference `m - r` is taken in `ℝ`; under `2r ≤ m` it is positive. The power `x^{-A}` with
real exponent is `Real.rpow`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Envelope bound on the lower half.** For real `A ≥ 0`, `m ≥ 1` and `r ∈ ℕ` with
`2r ≤ m`, `(m - r)^{-A} ≤ m^{-A} e^{2Ar/m}`. -/
@[collatz_pos_dens "lem_mo_envelope_half"]
theorem sub_rpow_neg_le_mul_exp_of_two_mul_le {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 1 ≤ m)
    {r : ℕ} (hr : 2 * r ≤ m) :
    ((m : ℝ) - r) ^ (-A) ≤ (m : ℝ) ^ (-A) * Real.exp (2 * A * r / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : (2 * r : ℝ) ≤ m := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hM0 : (0 : ℝ) < m - r := by linarith
  -- the case `A = 1`, in multiplicative form
  have base : (m : ℝ) ≤ (m - r) * Real.exp (2 * r / m) := by
    calc (m : ℝ) ≤ m + r * (m - 2 * r) / m :=
          le_add_of_nonneg_right <| div_nonneg (by nlinarith) hm0.le
      _ = (m - r) * (1 + 2 * r / m) := by
          field_simp
          ring
      _ ≤ _ := by
          gcongr
          linarith [Real.add_one_le_exp (2 * r / m)]
  have hE : Real.exp (2 * A * r / m) = Real.exp (2 * r / m) ^ A := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have key : (m : ℝ) ^ A ≤ ((m : ℝ) - r) ^ A * Real.exp (2 * r / m) ^ A := by
    rw [← Real.mul_rpow hM0.le (Real.exp_pos _).le]
    exact Real.rpow_le_rpow hm0.le base hA
  have hmA : 0 < (m : ℝ) ^ A := Real.rpow_pos_of_pos hm0 A
  have hMA : 0 < ((m : ℝ) - r) ^ A := Real.rpow_pos_of_pos hM0 A
  rwa [Real.rpow_neg hM0.le, Real.rpow_neg hm0.le, hE, ← div_eq_inv_mul,
    le_div_iff₀ hmA, inv_mul_eq_div, div_le_iff₀ hMA, mul_comm (Real.exp _ ^ A)]

end CollatzPosDens
