/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Basic

/-!
# The size factors of the trace schedule

For each Fourier parameter index `ι : FIndex` this file defines a sequence of positive natural
numbers `Kstar ι i`, the size factors of the trace schedule. At `ι = .o` the first nine values are
`4638, 1622, 1253, 971, 754, 587, 458, 359, 292`, and at `ι = .b` the first three values are
`718, 268, 1024`; every later value is `2^30`. All values are at least `268`.

## Main definitions

* `CollatzPosDens.Kstar`: the size factor `Kstar ι i : ℕ`, indexed by `ι : FIndex` and `i : ℕ`.

## Main results

* `CollatzPosDens.Kstar_o_eq_getD`, `CollatzPosDens.Kstar_b_eq_getD`: the size factors as list
  entries with default `2^30`.
* `CollatzPosDens.Kstar_o_zero`, …, `CollatzPosDens.Kstar_o_eight` and
  `CollatzPosDens.Kstar_b_zero`, `CollatzPosDens.Kstar_b_one`, `CollatzPosDens.Kstar_b_two`: the
  values below `2^30`.
* `CollatzPosDens.Kstar_o_of_nine_le`, `CollatzPosDens.Kstar_b_of_three_le`: the value `2^30` at
  the remaining indices.
* `CollatzPosDens.le_Kstar`, `CollatzPosDens.le_Kstar_o`, `CollatzPosDens.le_Kstar_b`,
  `CollatzPosDens.Kstar_pos`: `268 ≤ Kstar ι i`, `292 ≤ Kstar .o i`, `268 ≤ Kstar .b i` and
  `0 < Kstar ι i`.

## Implementation notes

The definition is total on `ℕ`, taking the value `2^30` at every index past the listed values.
-/

@[expose] public section

namespace CollatzPosDens

/-- The size factors of the trace schedule at the Fourier parameter index `ι`: the values
`Kstar .o i` for `i = 0, …, 8` are `4638, 1622, 1253, 971, 754, 587, 458, 359, 292` and
`Kstar .o i = 2^30` for `i ≥ 9`; the values `Kstar .b i` for `i = 0, 1, 2` are `718, 268, 1024`
and `Kstar .b i = 2^30` for `i ≥ 3`. -/
@[collatz_pos_dens "def_s02_K"]
def Kstar : FIndex → ℕ → ℕ
  | .o, i => [4638, 1622, 1253, 971, 754, 587, 458, 359, 292].getD i (2 ^ 30)
  | .b, i => [718, 268, 1024].getD i (2 ^ 30)

/-- The size factor `Kstar .o i` as the `i`-th entry of the list of the first nine values, with
default `2^30`. -/
theorem Kstar_o_eq_getD (i : ℕ) :
    Kstar .o i = [4638, 1622, 1253, 971, 754, 587, 458, 359, 292].getD i (2 ^ 30) := rfl

/-- The size factor `Kstar .b i` as the `i`-th entry of the list of the first three values, with
default `2^30`. -/
theorem Kstar_b_eq_getD (i : ℕ) :
    Kstar .b i = [718, 268, 1024].getD i (2 ^ 30) := rfl

/-- The size factor `Kstar .o 0` equals `4638`. -/
@[simp] theorem Kstar_o_zero : Kstar .o 0 = 4638 := rfl
/-- The size factor `Kstar .o 1` equals `1622`. -/
@[simp] theorem Kstar_o_one : Kstar .o 1 = 1622 := rfl
/-- The size factor `Kstar .o 2` equals `1253`. -/
@[simp] theorem Kstar_o_two : Kstar .o 2 = 1253 := rfl
/-- The size factor `Kstar .o 3` equals `971`. -/
@[simp] theorem Kstar_o_three : Kstar .o 3 = 971 := rfl
/-- The size factor `Kstar .o 4` equals `754`. -/
@[simp] theorem Kstar_o_four : Kstar .o 4 = 754 := rfl
/-- The size factor `Kstar .o 5` equals `587`. -/
@[simp] theorem Kstar_o_five : Kstar .o 5 = 587 := rfl
/-- The size factor `Kstar .o 6` equals `458`. -/
@[simp] theorem Kstar_o_six : Kstar .o 6 = 458 := rfl
/-- The size factor `Kstar .o 7` equals `359`. -/
@[simp] theorem Kstar_o_seven : Kstar .o 7 = 359 := rfl
/-- The size factor `Kstar .o 8` equals `292`. -/
@[simp] theorem Kstar_o_eight : Kstar .o 8 = 292 := rfl

/-- The size factor `Kstar .b 0` equals `718`. -/
@[simp] theorem Kstar_b_zero : Kstar .b 0 = 718 := rfl
/-- The size factor `Kstar .b 1` equals `268`. -/
@[simp] theorem Kstar_b_one : Kstar .b 1 = 268 := rfl
/-- The size factor `Kstar .b 2` equals `1024`. -/
@[simp] theorem Kstar_b_two : Kstar .b 2 = 1024 := rfl

/-- The size factor `Kstar .o i` equals `2^30` for `i ≥ 9`. -/
theorem Kstar_o_of_nine_le {i : ℕ} (h : 9 ≤ i) : Kstar .o i = 2 ^ 30 := by
  rw [Kstar_o_eq_getD, List.getD_eq_default _ _ (by simpa using h)]

/-- The size factor `Kstar .b i` equals `2^30` for `i ≥ 3`. -/
theorem Kstar_b_of_three_le {i : ℕ} (h : 3 ≤ i) : Kstar .b i = 2 ^ 30 := by
  rw [Kstar_b_eq_getD, List.getD_eq_default _ _ (by simpa using h)]

/-- Every size factor at the original index is at least `292 = Kstar .o 8`. -/
theorem le_Kstar_o (i : ℕ) : 292 ≤ Kstar .o i := by
  rcases lt_or_ge i 9 with h | h
  · interval_cases i <;> simp
  · rw [Kstar_o_of_nine_le h]; norm_num

/-- Every size factor at the bootstrap index is at least `268 = Kstar .b 1`. -/
theorem le_Kstar_b (i : ℕ) : 268 ≤ Kstar .b i := by
  rcases lt_or_ge i 3 with h | h
  · interval_cases i <;> simp
  · rw [Kstar_b_of_three_le h]; norm_num

/-- Every size factor is at least `268`. -/
theorem le_Kstar (ι : FIndex) (i : ℕ) : 268 ≤ Kstar ι i := by
  cases ι
  · exact le_trans (by norm_num) (le_Kstar_o i)
  · exact le_Kstar_b i

/-- Every size factor is positive. -/
theorem Kstar_pos (ι : FIndex) (i : ℕ) : 0 < Kstar ι i :=
  lt_of_lt_of_le (by norm_num) (le_Kstar ι i)

end CollatzPosDens
