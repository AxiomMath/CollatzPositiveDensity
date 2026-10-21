/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr

/-!
# The number of offset shells

For a natural number `n`, the number of offset shells is the natural number
`J^sh_n = ⌈2 log₂ n⌉₊`. Offset shells are indexed by `j ≤ J^sh_n`.

## Main definitions

* `CollatzPosDens.shJ`: the number of offset shells `J^sh_n = ⌈2 log₂ n⌉₊`.

## Main results

* `CollatzPosDens.le_shJ`, `CollatzPosDens.shJ_lt_add_one`: `J^sh_n` is the ceiling of
  `2 log₂ n`, so `2 log₂ n ≤ J^sh_n < 2 log₂ n + 1`.
* `CollatzPosDens.shJ_le_iff`: `J^sh_n ≤ m ↔ 2 log₂ n ≤ m`.
* `CollatzPosDens.shJ_mono`: `n ↦ J^sh_n` is monotone.
* `CollatzPosDens.shJ_pos`: `0 < J^sh_n` for `n ≥ 2`.

## Implementation notes

The definition is stated for every `n : ℕ`; for `n ∈ {0, 1}` the logarithm vanishes and the
number of shells is `0`. The hypothesis `n ≥ 1` is carried by the lemmas that need it rather than
by the definition.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The number of offset shells, `J^sh_n = ⌈2 log₂ n⌉ ∈ ℕ`. -/
@[collatz_pos_dens "def_mx_sh_J"]
noncomputable def shJ (n : ℕ) : ℕ :=
  ⌈2 * Real.logb 2 n⌉₊

/-- `J^sh_n = ⌈2 log₂ n⌉₊`. -/
theorem shJ_def (n : ℕ) : shJ n = ⌈2 * Real.logb 2 n⌉₊ := rfl

private theorem logb_two_natCast_nonneg (n : ℕ) : 0 ≤ Real.logb 2 n :=
  div_nonneg (Real.log_natCast_nonneg n) (Real.log_nonneg one_le_two)

/-- `2 log₂ n ≤ J^sh_n`. -/
theorem le_shJ (n : ℕ) : 2 * Real.logb 2 n ≤ shJ n :=
  Nat.le_ceil _

/-- `J^sh_n < 2 log₂ n + 1`. -/
theorem shJ_lt_add_one (n : ℕ) : (shJ n : ℝ) < 2 * Real.logb 2 n + 1 :=
  Nat.ceil_lt_add_one (mul_nonneg zero_le_two (logb_two_natCast_nonneg n))

/-- `J^sh_n ≤ m` exactly when `2 log₂ n ≤ m`. -/
theorem shJ_le_iff {n m : ℕ} : shJ n ≤ m ↔ 2 * Real.logb 2 n ≤ m :=
  Nat.ceil_le

/-- `J^sh_0 = 0`. -/
@[simp]
theorem shJ_zero : shJ 0 = 0 := by
  simp [shJ]

/-- `J^sh_1 = 0`. -/
@[simp]
theorem shJ_one : shJ 1 = 0 := by
  simp [shJ]

/-- The number of offset shells `J^sh_n` is monotone in `n`. -/
theorem shJ_mono : Monotone shJ := by
  intro n m hnm
  unfold shJ
  gcongr ⌈2 * ?_⌉₊
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using logb_two_natCast_nonneg m
  · exact Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hn) (by exact_mod_cast hnm)

/-- For `n ≥ 2` the number of offset shells `J^sh_n` is positive. -/
theorem shJ_pos {n : ℕ} (hn : 2 ≤ n) : 0 < shJ n := by
  unfold shJ
  rw [Nat.ceil_pos]
  have := Real.logb_pos one_lt_two (show (1 : ℝ) < n by exact_mod_cast hn)
  positivity

end CollatzPosDens
