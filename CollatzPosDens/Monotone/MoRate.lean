/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The case-one rate function

For a real `A ≥ 0` and an integer `m ≥ 1`, the case-one rate is
`rt_A(m) := 4A(1 + log m)/m`, with `log` the natural logarithm. It is the rate appearing in
exponential envelopes of the form `max(m - r, 1)^{-A} ≤ m^{-A} exp(rt_A(m) r)`.

## Main definitions

* `CollatzPosDens.moRate A m`: the rate `rt_A(m) = 4A(1 + log m)/m`.

## Main results

* `CollatzPosDens.moRate_def`: the defining formula.
* `CollatzPosDens.moRate_nonneg`: `0 ≤ rt_A(m)` for `0 ≤ A`.
* `CollatzPosDens.moRate_pos`: `0 < rt_A(m)` when `0 < A` and `1 ≤ m`.
* `CollatzPosDens.moRate_mono_left`: `rt_A(m)` is monotone in `A`.
* `CollatzPosDens.moRate_mul_natCast`: `rt_A(m) · m = 4A(1 + log m)` for `m ≥ 1`.

## Implementation notes

The function is defined for every real `A` and every `m : ℕ`; at `m = 0` it takes the junk
value `0` (division by zero in `ℝ`). The hypotheses `A ≥ 0` and `m ≥ 1` are carried by the
lemmas that need them rather than by the definition.

## References

* [Mazur, *Collatz positive density*], §8.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The case-one rate `rt_A(m) := 4A(1 + log m)/m`, for real `A` and `m ∈ ℕ`
(meaningful for `A ≥ 0`, `m ≥ 1`). -/
@[collatz_pos_dens "def_mo_rate"]
noncomputable def moRate (A : ℝ) (m : ℕ) : ℝ :=
  4 * A * (1 + Real.log m) / m

/-- The defining formula of `moRate`. -/
theorem moRate_def (A : ℝ) (m : ℕ) : moRate A m = 4 * A * (1 + Real.log m) / m := rfl

/-- The rate vanishes for `A = 0`. -/
@[simp]
theorem moRate_zero_left (m : ℕ) : moRate 0 m = 0 := by simp [moRate]

/-- The junk value at `m = 0` is `0`. -/
@[simp]
theorem moRate_zero_right (A : ℝ) : moRate A 0 = 0 := by simp [moRate]

/-- At `m = 1` the rate is `4A`. -/
@[simp]
theorem moRate_one_right (A : ℝ) : moRate A 1 = 4 * A := by simp [moRate]

/-- Clearing the denominator: `rt_A(m) · m = 4A(1 + log m)` for `m ≥ 1`. -/
theorem moRate_mul_natCast (A : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    moRate A m * m = 4 * A * (1 + Real.log m) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [moRate, div_mul_cancel₀ _ hm']

/-- The rate is nonnegative for `0 ≤ A`. -/
theorem moRate_nonneg {A : ℝ} (hA : 0 ≤ A) (m : ℕ) : 0 ≤ moRate A m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  unfold moRate
  positivity

/-- The rate is positive when `0 < A` and `1 ≤ m`. -/
theorem moRate_pos {A : ℝ} {m : ℕ} (hA : 0 < A) (hm : 1 ≤ m) : 0 < moRate A m := by
  have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold moRate
  positivity

/-- The rate is monotone in `A`. -/
theorem moRate_mono_left {A B : ℝ} (h : A ≤ B) (m : ℕ) : moRate A m ≤ moRate B m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  unfold moRate
  gcongr

end CollatzPosDens
