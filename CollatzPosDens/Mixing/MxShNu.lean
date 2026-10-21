/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr

/-!
# The exposure length of the shell cut

For an integer `n ≥ 1`, the exposure length of the shell cut is the natural number
`ν^sh_n = ⌈2048 log n⌉`, the least natural number that is at least `2048 log n`.

## Main definitions

* `CollatzPosDens.shNu`: the exposure length `ν^sh_n = ⌈2048 log n⌉₊`.

## Main results

* `CollatzPosDens.le_shNu`, `CollatzPosDens.shNu_lt_add_one`: `ν^sh_n` is the ceiling of
  `2048 log n`, so `2048 log n ≤ ν^sh_n < 2048 log n + 1`.
* `CollatzPosDens.shNu_le_iff`: `ν^sh_n ≤ m ↔ 2048 log n ≤ m`.
* `CollatzPosDens.shNu_mono`: `n ↦ ν^sh_n` is monotone.
* `CollatzPosDens.shNu_pos`: `0 < ν^sh_n` for `n ≥ 2`.

## Implementation notes

The definition is stated for every `n : ℕ`; for `n ∈ {0, 1}` the logarithm vanishes and the
exposure length is `0`. A hypothesis on `n` is carried by the lemmas that need it rather than by
the definition.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The exposure length of the shell cut, `ν^sh_n = ⌈2048 log n⌉ ∈ ℕ`. -/
@[collatz_pos_dens "def_mx_sh_nu"]
noncomputable def shNu (n : ℕ) : ℕ :=
  ⌈2048 * Real.log n⌉₊

/-- `ν^sh_n` is `⌈2048 log n⌉₊`. -/
theorem shNu_def (n : ℕ) : shNu n = ⌈2048 * Real.log n⌉₊ := rfl

/-- `2048 log n ≤ ν^sh_n`. -/
theorem le_shNu (n : ℕ) : 2048 * Real.log n ≤ shNu n :=
  Nat.le_ceil _

/-- `ν^sh_n < 2048 log n + 1`. -/
theorem shNu_lt_add_one (n : ℕ) : (shNu n : ℝ) < 2048 * Real.log n + 1 :=
  Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n))

/-- `ν^sh_n ≤ m` exactly when `2048 log n ≤ m`. -/
theorem shNu_le_iff {n m : ℕ} : shNu n ≤ m ↔ 2048 * Real.log n ≤ m :=
  Nat.ceil_le

/-- `ν^sh_0 = 0`. -/
@[simp]
theorem shNu_zero : shNu 0 = 0 := by
  simp [shNu]

/-- `ν^sh_1 = 0`. -/
@[simp]
theorem shNu_one : shNu 1 = 0 := by
  simp [shNu]

/-- The exposure length `ν^sh_n` is monotone in `n`. -/
theorem shNu_mono : Monotone shNu := by
  intro n m hnm
  unfold shNu
  gcongr ⌈2048 * ?_⌉₊
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Real.log_natCast_nonneg m
  · exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnm)

/-- For `n ≥ 2` the exposure length `ν^sh_n` is positive. -/
theorem shNu_pos {n : ℕ} (hn : 2 ≤ n) : 0 < shNu n := by
  unfold shNu
  rw [Nat.ceil_pos]
  have := Real.log_pos (show (1 : ℝ) < n by exact_mod_cast hn)
  positivity

end CollatzPosDens
