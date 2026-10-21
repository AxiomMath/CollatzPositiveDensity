/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Order.Basic
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# The cutoff of the gap-zero tree

This file defines the cutoff `cut⁰ : ℕ → ℕ` of the gap-zero tree, given by
`cut⁰(h) = min {12, 17 - h}` for `h ≤ 17` and `cut⁰(h) = 0` for `h > 17`. At depth `h` the tree
explores at most `cut⁰(h)` further levels, so it never reaches past height `17`, and no single step
exceeds `12` levels.

## Main definitions

* `CollatzPosDens.trZeroCutoff`: the cutoff `cut⁰`.

## Main results

* `CollatzPosDens.trZeroCutoff_eq_min`: `cut⁰(h) = min 12 (17 - h)` for every `h`, with
  truncated subtraction on `ℕ`.
* `CollatzPosDens.trZeroCutoff_zero`: `cut⁰(0) = 12`.
* `CollatzPosDens.trZeroCutoff_le_twelve`: `cut⁰(h) ≤ 12`.
* `CollatzPosDens.add_trZeroCutoff_le_seventeen`: `h + cut⁰(h) ≤ 17` for `h ≤ 17`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The cutoff of the gap-zero tree: `cut⁰(h) = min {12, 17 - h}` if `h ≤ 17`, and
`cut⁰(h) = 0` if `h > 17`. -/
@[collatz_pos_dens "def_tr_zero_cutoff"]
def trZeroCutoff (h : ℕ) : ℕ :=
  if h ≤ 17 then min 12 (17 - h) else 0

/-- For `h ≤ 17`, `cut⁰(h) = min 12 (17 - h)`. -/
theorem trZeroCutoff_of_le {h : ℕ} (hh : h ≤ 17) : trZeroCutoff h = min 12 (17 - h) :=
  ite_eq_left hh

/-- For `h > 17`, `cut⁰(h) = 0`. -/
theorem trZeroCutoff_of_lt {h : ℕ} (hh : 17 < h) : trZeroCutoff h = 0 :=
  ite_eq_right (not_le.mpr hh)

/-- With truncated subtraction, `cut⁰(h) = min 12 (17 - h)` for every `h : ℕ`. -/
theorem trZeroCutoff_eq_min (h : ℕ) : trZeroCutoff h = min 12 (17 - h) := by
  unfold trZeroCutoff
  split_ifs with hh
  · rfl
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.min_zero]

/-- `cut⁰(0) = 12`. -/
@[simp]
theorem trZeroCutoff_zero : trZeroCutoff 0 = 12 := rfl

/-- `cut⁰(h) ≤ 12` for every `h`. -/
theorem trZeroCutoff_le_twelve (h : ℕ) : trZeroCutoff h ≤ 12 := by
  rw [trZeroCutoff_eq_min]
  exact min_le_left _ _

/-- `cut⁰(h) ≤ 17 - h` for every `h`, with truncated subtraction. -/
theorem trZeroCutoff_le_sub (h : ℕ) : trZeroCutoff h ≤ 17 - h := by
  rw [trZeroCutoff_eq_min]
  exact min_le_right _ _

/-- For `h ≤ 17`, `h + cut⁰(h) ≤ 17`. -/
theorem add_trZeroCutoff_le_seventeen {h : ℕ} (hh : h ≤ 17) : h + trZeroCutoff h ≤ 17 := by
  have := trZeroCutoff_le_sub h
  omega

/-- For `h ≤ 5`, `cut⁰(h) = 12`. -/
theorem trZeroCutoff_eq_twelve {h : ℕ} (hh : h ≤ 5) : trZeroCutoff h = 12 := by
  rw [trZeroCutoff_eq_min]
  omega

/-- For `h ≥ 5`, `cut⁰(h) = 17 - h`, with truncated subtraction. -/
theorem trZeroCutoff_eq_sub {h : ℕ} (hh : 5 ≤ h) : trZeroCutoff h = 17 - h := by
  rw [trZeroCutoff_eq_min]
  omega

/-- The cutoff `cut⁰` is antitone. -/
theorem trZeroCutoff_antitone : Antitone trZeroCutoff := fun a b hab => by
  rw [trZeroCutoff_eq_min, trZeroCutoff_eq_min]
  omega

end CollatzPosDens
