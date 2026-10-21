/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr

/-!
# The half-width of the shell window

For a natural number `n`, the half-width of the shell window is the natural number
`h^sh_n = ⌈√(128 n log n)⌉₊`, the least natural number at least `√(128 n log n)`.

## Main definitions

* `CollatzPosDens.shWidth`: the half-width `h^sh_n = ⌈√(128 n log n)⌉₊`.

## Main results

* `CollatzPosDens.sqrt_le_shWidth`, `CollatzPosDens.shWidth_lt_sqrt_add_one`: `h^sh_n` is the
  ceiling of `√(128 n log n)`, so `√(128 n log n) ≤ h^sh_n < √(128 n log n) + 1`.
* `CollatzPosDens.shWidth_le_iff`: `h^sh_n ≤ m ↔ √(128 n log n) ≤ m`.
* `CollatzPosDens.shWidth_mono`: `n ↦ h^sh_n` is monotone.
* `CollatzPosDens.shWidth_pos`: `0 < h^sh_n` for `n ≥ 2`.

## Implementation notes

The definition is stated for every `n : ℕ`; for `n ∈ {0, 1}` the logarithm vanishes and the
half-width is `0`. Lower bounds on `n` are hypotheses of the lemmas that need them rather than of
the definition.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

/-- The half-width of the shell window, `h^sh_n = ⌈√(128 n log n)⌉ ∈ ℕ`. -/
@[collatz_pos_dens "def_mx_sh_h"]
noncomputable def shWidth (n : ℕ) : ℕ :=
  ⌈Real.sqrt (128 * n * Real.log n)⌉₊

/-- `h^sh_n = ⌈√(128 n log n)⌉₊`. -/
theorem shWidth_def (n : ℕ) : shWidth n = ⌈Real.sqrt (128 * n * Real.log n)⌉₊ := rfl

/-- `√(128 n log n) ≤ h^sh_n`. -/
theorem sqrt_le_shWidth (n : ℕ) : Real.sqrt (128 * n * Real.log n) ≤ shWidth n :=
  Nat.le_ceil _

/-- `h^sh_n < √(128 n log n) + 1`. -/
theorem shWidth_lt_sqrt_add_one (n : ℕ) :
    (shWidth n : ℝ) < Real.sqrt (128 * n * Real.log n) + 1 :=
  Nat.ceil_lt_add_one (Real.sqrt_nonneg _)

/-- `h^sh_n ≤ m` exactly when `√(128 n log n) ≤ m`. -/
theorem shWidth_le_iff {n m : ℕ} : shWidth n ≤ m ↔ Real.sqrt (128 * n * Real.log n) ≤ m :=
  Nat.ceil_le

/-- `h^sh_0 = 0`. -/
@[simp]
theorem shWidth_zero : shWidth 0 = 0 := by
  simp [shWidth]

/-- `h^sh_1 = 0`. -/
@[simp]
theorem shWidth_one : shWidth 1 = 0 := by
  simp [shWidth]

/-- The half-width `h^sh_n` is monotone in `n`. -/
theorem shWidth_mono : Monotone shWidth := by
  intro n m hnm
  unfold shWidth
  gcongr ⌈Real.sqrt ?_⌉₊
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_mul]
    exact mul_nonneg (by positivity) (Real.log_natCast_nonneg m)
  · have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : Real.log n ≤ Real.log m := Real.log_le_log hn' hnm'
    have := Real.log_natCast_nonneg n
    gcongr

/-- For `n ≥ 2` the half-width `h^sh_n` is positive. -/
theorem shWidth_pos {n : ℕ} (hn : 2 ≤ n) : 0 < shWidth n := by
  unfold shWidth
  rw [Nat.ceil_pos, Real.sqrt_pos]
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_pos h1
  positivity

end CollatzPosDens
