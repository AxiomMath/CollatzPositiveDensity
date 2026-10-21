/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Table
public import CollatzPosDens.Case3.C3PacketPotential
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.IntervalCases

/-!
# The constants of the rows of the height-seventeen cost table

The Lipschitz constants `ℓ_c`, `3 ≤ c ≤ 16`, of the capped factors and `𝖫_h`, `1 ≤ h ≤ 14`, of
the future costs are explicit rationals. For each of the `135` rows `(c, o)`, `2 ≤ c ≤ 16`,
`1 ≤ o ≤ c`, the packet value `1 - δ'_{c,o} = p_n / p_d` (`1` for `c = 2`) and the two rounded
Lipschitz corrections `a_{dir} = ⌈10^8 · 10^{-6} ℓ_c 2^{-o}⌉`,
`a_{jo} = ⌈10^8 · 10^{-6} (ℓ_c 2^{-o} + 9 𝖫_o)⌉` are recorded in a table and certified by
kernel evaluation, the packet value in natural numbers (`CollatzPosDens.C3H17Values.RowConstOKN`).

## Main definitions

* `CollatzPosDens.C3H17Values.ellQ`, `CollatzPosDens.C3H17Values.lipQ`: the values of `ℓ_c` and
  `𝖫_h`.
* `CollatzPosDens.C3H17Values.constTab`: the table `(c, o, p_n, p_d, a_{dir}, a_{jo})`.

## Main results

* `CollatzPosDens.C3H17Values.trLipConst_eq_ellQ`, `CollatzPosDens.C3H17Values.c3H17Lip_eq_lipQ`:
  the values of the Lipschitz constants.
* `CollatzPosDens.C3H17Values.rowConst_spec`: the certified properties of a table entry.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The values of `ℓ_c`, `0 ≤ c ≤ 16` (`0` for `c ≤ 2`). -/
def ellQ (c : ℤ) : ℚ :=
  ([(0 : ℚ),
    (0 : ℚ),
    (0 : ℚ),
    (22 / 7 : ℚ),
    (44 / 7 : ℚ),
    (99 / 7 : ℚ),
    (132 / 5 : ℚ),
    (154 / 3 : ℚ),
    (660 / 7 : ℚ),
    (2475 / 14 : ℚ),
    (6820 / 21 : ℚ),
    (21142 / 35 : ℚ),
    (1116 : ℚ),
    (2079 : ℚ),
    (50292 / 13 : ℚ),
    (354838 / 49 : ℚ),
    (94996 / 7 : ℚ)] : List ℚ).getD c.toNat 0

/-- The values of `𝖫_h`, `0 ≤ h ≤ 15` (`0` for `h = 0` and `h = 15`). -/
def lipQ (h : ℤ) : ℚ :=
  ([(0 : ℚ),
    (638746537 / 1073741824 : ℚ),
    (1060936987 / 3758096384 : ℚ),
    (8932143 / 67108864 : ℚ),
    (14625039 / 234881024 : ℚ),
    (27107223 / 939524096 : ℚ),
    (6207531 / 469762048 : ℚ),
    (1400641 / 234881024 : ℚ),
    (44275 / 16777216 : ℚ),
    (9559 / 8388608 : ℚ),
    (13915 / 29360128 : ℚ),
    (1375 / 7340032 : ℚ),
    (253 / 3670016 : ℚ),
    (11 / 524288 : ℚ),
    (11 / 1835008 : ℚ),
    (0 : ℚ)] : List ℚ).getD h.toNat 0

/-- The value `ℓ_3 = 22 / 7`. -/
theorem trLipConst_3 : trLipConst 3 = 22 / 7 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_4 = 44 / 7`. -/
theorem trLipConst_4 : trLipConst 4 = 44 / 7 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_5 = 99 / 7`. -/
theorem trLipConst_5 : trLipConst 5 = 99 / 7 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_6 = 132 / 5`. -/
theorem trLipConst_6 : trLipConst 6 = 132 / 5 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_7 = 154 / 3`. -/
theorem trLipConst_7 : trLipConst 7 = 154 / 3 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_8 = 660 / 7`. -/
theorem trLipConst_8 : trLipConst 8 = 660 / 7 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_9 = 2475 / 14`. -/
theorem trLipConst_9 : trLipConst 9 = 2475 / 14 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_10 = 6820 / 21`. -/
theorem trLipConst_10 : trLipConst 10 = 6820 / 21 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_11 = 21142 / 35`. -/
theorem trLipConst_11 : trLipConst 11 = 21142 / 35 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_12 = 1116`. -/
theorem trLipConst_12 : trLipConst 12 = 1116 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_13 = 2079`. -/
theorem trLipConst_13 : trLipConst 13 = 2079 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_14 = 50292 / 13`. -/
theorem trLipConst_14 : trLipConst 14 = 50292 / 13 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_15 = 354838 / 49`. -/
theorem trLipConst_15 : trLipConst 15 = 354838 / 49 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- The value `ℓ_16 = 94996 / 7`. -/
theorem trLipConst_16 : trLipConst 16 = 94996 / 7 := by
  norm_num [trLipConst, Finset.sum_range_succ, abs_of_nonneg, abs_of_nonpos]

/-- `trLipConst c` agrees with the tabulated value `ellQ c` for `2 ≤ c ≤ 16`. -/
theorem trLipConst_eq_ellQ {c : ℤ} (h₂ : 2 ≤ c) (h₁₆ : c ≤ 16) :
    trLipConst c = ellQ c := by
  rcases (show c = 2 ∨ 3 ≤ c by omega) with rfl | h₃
  · rw [trLipConst_of_not_mem (by omega)]; rfl
  · interval_cases c
    · rw [trLipConst_3]; rfl
    · rw [trLipConst_4]; rfl
    · rw [trLipConst_5]; rfl
    · rw [trLipConst_6]; rfl
    · rw [trLipConst_7]; rfl
    · rw [trLipConst_8]; rfl
    · rw [trLipConst_9]; rfl
    · rw [trLipConst_10]; rfl
    · rw [trLipConst_11]; rfl
    · rw [trLipConst_12]; rfl
    · rw [trLipConst_13]; rfl
    · rw [trLipConst_14]; rfl
    · rw [trLipConst_15]; rfl
    · rw [trLipConst_16]; rfl

/-- The value `𝖫_14 = 11 / 1835008`. -/
theorem c3H17Lip_14 : c3H17Lip 14 = 11 / 1835008 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 14) =
      {3} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 14)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      ∅ by decide]
  norm_num [trLipConst_3,
    c3H17Lip_of_le]

/-- The value `𝖫_13 = 11 / 524288`. -/
theorem c3H17Lip_13 : c3H17Lip 13 = 11 / 524288 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 13) =
      {3, 4} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 13)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    c3H17Lip_of_le]

/-- The value `𝖫_12 = 253 / 3670016`. -/
theorem c3H17Lip_12 : c3H17Lip 12 = 253 / 3670016 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 12) =
      {3, 4, 5} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 12)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_11 = 1375 / 7340032`. -/
theorem c3H17Lip_11 : c3H17Lip 11 = 1375 / 7340032 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 11) =
      {3, 4, 5, 6} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 11)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    c3H17Lip_13,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_10 = 13915 / 29360128`. -/
theorem c3H17Lip_10 : c3H17Lip 10 = 13915 / 29360128 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 10) =
      {3, 4, 5, 6, 7} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 10)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    c3H17Lip_12,
    c3H17Lip_13,
    c3H17Lip_of_le]

/-- The value `𝖫_9 = 9559 / 8388608`. -/
theorem c3H17Lip_9 : c3H17Lip 9 = 9559 / 8388608 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 9) =
      {3, 4, 5, 6, 7, 8} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 9)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    c3H17Lip_11,
    c3H17Lip_12,
    c3H17Lip_of_le]

/-- The value `𝖫_8 = 44275 / 16777216`. -/
theorem c3H17Lip_8 : c3H17Lip 8 = 44275 / 16777216 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 8) =
      {3, 4, 5, 6, 7, 8, 9} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 8)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6, 7} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    trLipConst_9,
    c3H17Lip_10,
    c3H17Lip_11,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_7 = 1400641 / 234881024`. -/
theorem c3H17Lip_7 : c3H17Lip 7 = 1400641 / 234881024 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 7) =
      {3, 4, 5, 6, 7, 8, 9, 10} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 7)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6, 7, 8} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    trLipConst_9,
    trLipConst_10,
    c3H17Lip_9,
    c3H17Lip_10,
    c3H17Lip_13,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_6 = 6207531 / 469762048`. -/
theorem c3H17Lip_6 : c3H17Lip 6 = 6207531 / 469762048 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 6) =
      {3, 4, 5, 6, 7, 8, 9, 10, 11} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 6)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6, 7, 8, 9} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    trLipConst_9,
    trLipConst_10,
    trLipConst_11,
    c3H17Lip_8,
    c3H17Lip_9,
    c3H17Lip_12,
    c3H17Lip_13,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_5 = 27107223 / 939524096`. -/
theorem c3H17Lip_5 : c3H17Lip 5 = 27107223 / 939524096 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 5) =
      {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 5)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6, 7, 8, 9, 10} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    trLipConst_9,
    trLipConst_10,
    trLipConst_11,
    trLipConst_12,
    c3H17Lip_7,
    c3H17Lip_8,
    c3H17Lip_11,
    c3H17Lip_12,
    c3H17Lip_13,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_4 = 14625039 / 234881024`. -/
theorem c3H17Lip_4 : c3H17Lip 4 = 14625039 / 234881024 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 4) =
      {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 4)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6, 7, 8, 9, 10, 11} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    trLipConst_9,
    trLipConst_10,
    trLipConst_11,
    trLipConst_12,
    trLipConst_13,
    c3H17Lip_6,
    c3H17Lip_7,
    c3H17Lip_10,
    c3H17Lip_11,
    c3H17Lip_12,
    c3H17Lip_13,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_3 = 8932143 / 67108864`. -/
theorem c3H17Lip_3 : c3H17Lip 3 = 8932143 / 67108864 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 3) =
      {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 3)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6, 7, 8, 9, 10, 11, 12} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    trLipConst_9,
    trLipConst_10,
    trLipConst_11,
    trLipConst_12,
    trLipConst_13,
    trLipConst_14,
    c3H17Lip_5,
    c3H17Lip_6,
    c3H17Lip_9,
    c3H17Lip_10,
    c3H17Lip_11,
    c3H17Lip_12,
    c3H17Lip_13,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_2 = 1060936987 / 3758096384`. -/
theorem c3H17Lip_2 : c3H17Lip 2 = 1060936987 / 3758096384 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 2) =
      {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 2)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6, 7, 8, 9, 10, 11, 12, 13} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    trLipConst_9,
    trLipConst_10,
    trLipConst_11,
    trLipConst_12,
    trLipConst_13,
    trLipConst_14,
    trLipConst_15,
    c3H17Lip_4,
    c3H17Lip_5,
    c3H17Lip_8,
    c3H17Lip_9,
    c3H17Lip_10,
    c3H17Lip_11,
    c3H17Lip_12,
    c3H17Lip_13,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- The value `𝖫_1 = 638746537 / 1073741824`. -/
theorem c3H17Lip_1 : c3H17Lip 1 = 638746537 / 1073741824 := by
  rw [c3H17Lip_of_lt (by norm_num)]
  rw [show Finset.Icc (3 : ℤ) (17 - 1) =
      {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} by decide,
    show (Finset.Icc (2 : ℤ) (15 - 1)).filter (· ∉ ({4, 5} : Finset ℤ)) =
      {2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14} by decide]
  norm_num [trLipConst_3,
    trLipConst_4,
    trLipConst_5,
    trLipConst_6,
    trLipConst_7,
    trLipConst_8,
    trLipConst_9,
    trLipConst_10,
    trLipConst_11,
    trLipConst_12,
    trLipConst_13,
    trLipConst_14,
    trLipConst_15,
    trLipConst_16,
    c3H17Lip_3,
    c3H17Lip_4,
    c3H17Lip_7,
    c3H17Lip_8,
    c3H17Lip_9,
    c3H17Lip_10,
    c3H17Lip_11,
    c3H17Lip_12,
    c3H17Lip_13,
    c3H17Lip_14,
    c3H17Lip_of_le]

/-- `c3H17Lip h` agrees with the tabulated value `lipQ h` for `1 ≤ h ≤ 16`. -/
theorem c3H17Lip_eq_lipQ {h : ℤ} (h₁ : 1 ≤ h) (h₁₆ : h ≤ 16) :
    c3H17Lip h = lipQ h := by
  rcases (show h ≤ 14 ∨ 15 ≤ h by omega) with h₁₄ | h₁₅
  · interval_cases h
    · rw [c3H17Lip_1]; rfl
    · rw [c3H17Lip_2]; rfl
    · rw [c3H17Lip_3]; rfl
    · rw [c3H17Lip_4]; rfl
    · rw [c3H17Lip_5]; rfl
    · rw [c3H17Lip_6]; rfl
    · rw [c3H17Lip_7]; rfl
    · rw [c3H17Lip_8]; rfl
    · rw [c3H17Lip_9]; rfl
    · rw [c3H17Lip_10]; rfl
    · rw [c3H17Lip_11]; rfl
    · rw [c3H17Lip_12]; rfl
    · rw [c3H17Lip_13]; rfl
    · rw [c3H17Lip_14]; rfl
  · rw [c3H17Lip_of_le h₁₅]
    interval_cases h <;> rfl

/-- Part A of the table `(c, o, p_n, p_d, a_{dir}, a_{jo})` of the `135` rows. -/
def constTabA : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2, 1, 1, 1,
    0, 536),
  (2, 2, 1, 1,
    0, 255),
  (3, 1, 1, 65536,
    158, 693),
  (3, 2, 176777, 250000,
    79, 333),
  (3, 3, 23097, 25000,
    40, 160),
  (4, 1, 16667, 50000,
    315, 850),
  (4, 2, 333337, 1000000,
    158, 412),
  (4, 3, 72169, 125000,
    79, 199),
  (4, 4, 441819, 500000,
    40, 96),
  (5, 1, 100001, 200000,
    708, 1243),
  (5, 2, 8839, 25000,
    354, 608),
  (5, 3, 461943, 1000000,
    177, 297),
  (5, 4, 120911, 200000,
    89, 145),
  (5, 5, 433771, 500000,
    45, 71),
  (6, 1, 150001, 250000,
    1320, 1856),
  (6, 2, 15089, 31250,
    660, 915),
  (6, 3, 15089, 31250,
    330, 450),
  (6, 4, 1357283593, 2560000000,
    165, 222),
  (6, 5, 170911, 250000,
    83, 109),
  (6, 6, 864601, 1000000,
    42, 54),
  (7, 1, 66667, 100000,
    2567, 3103),
  (7, 2, 7113, 12500,
    1284, 1538),
  (7, 3, 7113, 12500,
    642, 762),
  (7, 4, 843953, 1500000,
    321, 377),
  (7, 5, 1776741641, 3072000000,
    161, 187),
  (7, 6, 1103953, 1500000,
    81, 93),
  (7, 7, 868067, 1000000,
    41, 46),
  (8, 1, 250001, 350000,
    4715, 5250),
  (8, 2, 27589, 43750,
    2358, 2612),
  (8, 3, 27589, 43750,
    1179, 1299),
  (8, 4, 156279, 250000,
    590, 646),
  (8, 5, 617851, 1000000,
    295, 321),
  (8, 6, 442678837, 716800000,
    148, 160),
  (8, 7, 1353953, 1750000,
    74, 80),
  (8, 8, 874299, 1000000,
    37, 40),
  (9, 1, 300001, 400000,
    8840, 9375),
  (9, 2, 33839, 50000,
    4420, 4674),
  (9, 3, 33839, 50000,
    2210, 2330),
  (9, 4, 1343953, 2000000,
    1105, 1161),
  (9, 5, 5324957, 8000000,
    553, 579),
  (9, 6, 1319303, 2000000,
    277, 289),
  (9, 7, 2666717449, 4096000000,
    139, 144),
  (9, 8, 1603953, 2000000,
    70, 72),
  (9, 9, 7120093, 8000000,
    35, 36),
  (10, 1, 38889, 50000,
    16239, 16774)]

/-- Part B of the table `(c, o, p_n, p_d, a_{dir}, a_{jo})` of the `135` rows. -/
def constTabB : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (10, 2, 13363, 18750,
    8120, 8374),
  (10, 3, 13363, 18750,
    4060, 4180),
  (10, 4, 1593953, 2250000,
    2030, 2086),
  (10, 5, 702773, 1000000,
    1015, 1041),
  (10, 6, 174367, 250000,
    508, 520),
  (10, 7, 1034737, 1500000,
    254, 260),
  (10, 8, 3133503241, 4608000000,
    127, 130),
  (10, 9, 1853953, 2250000,
    64, 65),
  (10, 10, 8120093, 9000000,
    32, 33),
  (11, 1, 400001, 500000,
    30203, 30739),
  (11, 2, 46339, 62500,
    15102, 15356),
  (11, 3, 46339, 62500,
    7551, 7671),
  (11, 4, 1843953, 2500000,
    3776, 3832),
  (11, 5, 7324957, 10000000,
    1888, 1914),
  (11, 6, 1819303, 2500000,
    944, 956),
  (11, 7, 3604211, 5000000,
    472, 478),
  (11, 8, 7120113, 10000000,
    236, 239),
  (11, 9, 3645503241, 5120000000,
    118, 120),
  (11, 10, 2103953, 2500000,
    59, 60),
  (11, 11, 9120093, 10000000,
    30, 30),
  (12, 1, 450001, 550000,
    55800, 56336),
  (12, 2, 52589, 68750,
    27900, 28155),
  (12, 3, 52589, 68750,
    13950, 14070),
  (12, 4, 2093953, 2750000,
    6975, 7032),
  (12, 5, 8324957, 11000000,
    3488, 3514),
  (12, 6, 2069303, 2750000,
    1744, 1756),
  (12, 7, 4104211, 5500000,
    872, 878),
  (12, 8, 8120113, 11000000,
    436, 439),
  (12, 9, 8120113, 11000000,
    218, 219),
  (12, 10, 4157503241, 5632000000,
    109, 110),
  (12, 11, 2353953, 2750000,
    55, 55),
  (12, 12, 10120093, 11000000,
    28, 28),
  (13, 1, 166667, 200000,
    103950, 104486),
  (13, 2, 19613, 25000,
    51975, 52230),
  (13, 3, 19613, 25000,
    25988, 26108),
  (13, 4, 2343953, 3000000,
    12994, 13050),
  (13, 5, 3108319, 4000000,
    6497, 6523),
  (13, 6, 773101, 1000000,
    3249, 3261),
  (13, 7, 1534737, 2000000,
    1625, 1630),
  (13, 8, 9120113, 12000000,
    813, 815),
  (13, 9, 9120113, 12000000,
    407, 408),
  (13, 10, 9120113, 12000000,
    204, 204),
  (13, 11, 4669503241, 6144000000,
    102, 102),
  (13, 12, 2603953, 3000000,
    51, 51),
  (13, 13, 11120093, 12000000,
    26, 26)]

/-- Part C of the table `(c, o, p_n, p_d, a_{dir}, a_{jo})` of the `135` rows. -/
def constTabC : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (14, 1, 550001, 650000,
    193431, 193967),
  (14, 2, 65089, 81250,
    96716, 96970),
  (14, 3, 65089, 81250,
    48358, 48478),
  (14, 4, 2593953, 3250000,
    24179, 24235),
  (14, 5, 10324957, 13000000,
    12090, 12116),
  (14, 6, 2569303, 3250000,
    6045, 6057),
  (14, 7, 5104211, 6500000,
    3023, 3028),
  (14, 8, 10120113, 13000000,
    1512, 1514),
  (14, 9, 10120113, 13000000,
    756, 757),
  (14, 10, 10120113, 13000000,
    378, 379),
  (14, 11, 10120113, 13000000,
    189, 190),
  (14, 12, 5181503241, 6656000000,
    95, 95),
  (14, 13, 2853953, 3250000,
    48, 48),
  (14, 14, 12120093, 13000000,
    24, 24),
  (15, 1, 600001, 700000,
    362080, 362615),
  (15, 2, 71339, 87500,
    181040, 181294),
  (15, 3, 71339, 87500,
    90520, 90640),
  (15, 4, 406279, 500000,
    45260, 45316),
  (15, 5, 1617851, 2000000,
    22630, 22656),
  (15, 6, 2819303, 3500000,
    11315, 11327),
  (15, 7, 5604211, 7000000,
    5658, 5663),
  (15, 8, 11120113, 14000000,
    2829, 2832),
  (15, 9, 11120113, 14000000,
    1415, 1416),
  (15, 10, 11120113, 14000000,
    708, 708),
  (15, 11, 11120113, 14000000,
    354, 354),
  (15, 12, 11120113, 14000000,
    177, 177),
  (15, 13, 5693503241, 7168000000,
    89, 89),
  (15, 14, 3103953, 3500000,
    45, 45),
  (15, 15, 1874299, 2000000,
    23, 23),
  (16, 1, 216667, 250000,
    678543, 679079),
  (16, 2, 25863, 31250,
    339272, 339526),
  (16, 3, 25863, 31250,
    169636, 169756),
  (16, 4, 3093953, 3750000,
    84818, 84874),
  (16, 5, 4108319, 5000000,
    42409, 42435),
  (16, 6, 1023101, 1250000,
    21205, 21217),
  (16, 7, 2034737, 2500000,
    10603, 10608),
  (16, 8, 12120113, 15000000,
    5302, 5304),
  (16, 9, 12120113, 15000000,
    2651, 2652),
  (16, 10, 12120113, 15000000,
    1326, 1326),
  (16, 11, 12120113, 15000000,
    663, 663),
  (16, 12, 12120113, 15000000,
    332, 332),
  (16, 13, 12120113, 15000000,
    166, 166),
  (16, 14, 6205503241, 7680000000,
    83, 83),
  (16, 15, 3353953, 3750000,
    42, 42),
  (16, 16, 14120093, 15000000,
    21, 21)]

/-- The table `(c, o, p_n, p_d, a_{dir}, a_{jo})` of the `135` rows. -/
def constTab : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := constTabA ++ constTabB ++ constTabC

/-- The properties of a table entry, with `ℓ_c`, `𝖫_o` and the packet deficit in computable
form. -/
def RowConstOK (e : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  let c := e.1; let o := e.2.1; let pn := e.2.2.1; let pd := e.2.2.2.1
  let adir := e.2.2.2.2.1; let ajo := e.2.2.2.2.2
  0 < pd ∧ (3 ≤ c → (pn : ℚ) / pd =
      1 - min (c3PacketPotential c o 0 / ((c : ℤ) - 1)) (1 - (2 ^ 16 : ℚ)⁻¹)) ∧
    (c < 3 → pn = pd) ∧
    ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (ellQ c * 2 ^ (-(o : ℤ))))⌉ = adir ∧
    ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (ellQ c * 2 ^ (-(o : ℤ)) + 9 * lipQ o))⌉ = ajo

/-- `RowConstOK` is decidable. -/
instance (e : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Decidable (RowConstOK e) := by
  unfold RowConstOK; infer_instance

/-- `19110 ℓ_c` in natural numbers, `0 ≤ c ≤ 16`. -/
def ellN (c : ℕ) : ℕ :=
  [0, 0, 0, 60060, 120120, 270270, 504504, 980980, 1801800, 3378375, 6206200, 11543532,
    21326760, 39729690, 73929240, 138386820, 259339080].getD c 0

/-- `7 · 2^{30} 𝖫_h` in natural numbers, `0 ≤ h ≤ 15`. -/
def lipN (h : ℕ) : ℕ :=
  [0, 4471225759, 2121873974, 1000400016, 468001248, 216857784, 99320496, 44820512, 19835200,
    8564864, 3562240, 1408000, 518144, 157696, 45056, 0].getD h 0

/-- `ℓ_c = ellN c / 19110` for every natural `c`. -/
theorem ellQ_natCast (c : ℕ) : ellQ c = (ellN c : ℚ) / 19110 := by
  unfold ellQ ellN
  rw [Int.toNat_natCast]
  refine Eq.trans ?_ (List.getD_map _ 0 (n := c) (fun x : ℕ => (x : ℚ) / 19110))
  norm_num

/-- `𝖫_h = lipN h / (7 · 2^{30})` for every natural `h`. -/
theorem lipQ_natCast (h : ℕ) : lipQ h = (lipN h : ℚ) / 7516192768 := by
  unfold lipQ lipN
  rw [Int.toNat_natCast]
  refine Eq.trans ?_ (List.getD_map _ 0 (n := h) (fun x : ℕ => (x : ℚ) / 7516192768))
  norm_num

/-- `⌈N / D⌉ = a` from `N ≤ a D < N + D`, in natural numbers. -/
theorem ceil_natCast_div_eq {N D a : ℕ} (hD : 0 < D) (h₁ : N ≤ a * D) (h₂ : a * D < N + D) :
    ⌈(N : ℚ) / D⌉ = a := by
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  rw [Int.ceil_eq_iff]
  push_cast
  constructor
  · rw [lt_div_iff₀ hD']
    have : ((a * D : ℕ) : ℚ) < N + D := by exact_mod_cast h₂
    push_cast at this
    linarith
  · rw [div_le_iff₀ hD']
    exact_mod_cast h₁

/-- `RowConstOK` with the packet value condition in natural-number arithmetic: with
`Q = 1024000000 · 2^16 (c - 1)` and `F(0) = c3PotN c o 0 / 1024000000`, the condition
`p_n / p_d = 1 - min (F(0) / (c - 1)) (1 - 2^{-16})` reads `p_n Q = (Q - m) p_d`, where
`m = min (2^16 c3PotN c o 0) ((2^16 - 1) 1024000000 (c - 1))`; and the two ceilings, with
`ℓ_c = ellN c / 19110` and `𝖫_o = lipN o / (7 · 2^{30})`, as the inequalities `N ≤ a D < N + D`
characterising `⌈N / D⌉ = a`. -/
def RowConstOKN (e : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  let c := e.1; let o := e.2.1; let pn := e.2.2.1; let pd := e.2.2.2.1
  let adir := e.2.2.2.2.1; let ajo := e.2.2.2.2.2
  0 < pd ∧ (3 ≤ c → pn * (1024000000 * 65536 * (c - 1)) =
      (1024000000 * 65536 * (c - 1) -
        min (65536 * c3PotN c o 0) (65535 * 1024000000 * (c - 1))) * pd) ∧
    (c < 3 → pn = pd) ∧
    100 * ellN c ≤ adir * (19110 * 2 ^ o) ∧
      adir * (19110 * 2 ^ o) < 100 * ellN c + 19110 * 2 ^ o ∧
    100 * (ellN c * 7516192768 + 9 * lipN o * (19110 * 2 ^ o)) ≤
        ajo * (19110 * 7516192768 * 2 ^ o) ∧
      ajo * (19110 * 7516192768 * 2 ^ o) <
        100 * (ellN c * 7516192768 + 9 * lipN o * (19110 * 2 ^ o)) + 19110 * 7516192768 * 2 ^ o

/-- `RowConstOKN` is decidable. -/
instance (e : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Decidable (RowConstOKN e) := by
  unfold RowConstOKN; infer_instance

/-- The packet value condition of `RowConstOKN` implies the one of `RowConstOK`. -/
private theorem packet_value_eq {c P pn pd : ℕ} (hc : 3 ≤ c) (hpd : 0 < pd)
    (h : pn * (1024000000 * 65536 * (c - 1)) =
      (1024000000 * 65536 * (c - 1) - min (65536 * P) (65535 * 1024000000 * (c - 1))) * pd) :
    (pn : ℚ) / pd =
      1 - min ((P : ℚ) / 1024000000 / (((c : ℤ) : ℚ) - 1)) (1 - (2 ^ 16 : ℚ)⁻¹) := by
  set Q := 1024000000 * 65536 * (c - 1) with hQ
  set m := min (65536 * P) (65535 * 1024000000 * (c - 1)) with hm
  have hmQ : m ≤ Q := (min_le_right _ _).trans (by rw [hQ]; omega)
  have hc1 : (((c : ℤ) : ℚ) - 1) = ((c - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ c), Int.cast_natCast, Nat.cast_one]
  have hpos : (0 : ℚ) < ((c - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < c - 1)
  have hQpos : (0 : ℚ) < Q := by rw [hQ]; push_cast; positivity
  have h1 : (pn : ℚ) / pd = ((Q - m : ℕ) : ℚ) / Q := by
    rw [div_eq_div_iff (by exact_mod_cast hpd.ne') hQpos.ne']
    exact_mod_cast h
  have h2 : (m : ℚ) / Q = min ((P : ℚ) / 1024000000 / ((c - 1 : ℕ) : ℚ)) (1 - (2 ^ 16 : ℚ)⁻¹) := by
    rw [hm, Nat.cast_min, ← min_div_div_right hQpos.le]
    congr 1
    · rw [hQ]; push_cast; field_simp; ring
    · rw [hQ]; push_cast; field_simp; norm_num
  rw [h1, Nat.cast_sub hmQ, sub_div, div_self hQpos.ne', h2, hc1]

/-- The natural-number conditions imply `RowConstOK`. -/
theorem RowConstOKN.ok {e : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (h : RowConstOKN e) : RowConstOK e := by
  obtain ⟨c, o, pn, pd, adir, ajo⟩ := e
  dsimp only [RowConstOKN] at h
  dsimp only [RowConstOK]
  obtain ⟨h1, h2, h3, h4, h4', h5, h5'⟩ := h
  refine ⟨h1, fun hc => ?_, h3, ?_, ?_⟩
  · rw [c3PacketPotential_eq_c3PotN]
    exact packet_value_eq hc h1 (h2 hc)
  · rw [← ceil_natCast_div_eq (by positivity) h4 h4', ellQ_natCast, zpow_neg, zpow_natCast]
    push_cast
    congr 1
    field_simp
    ring
  · rw [← ceil_natCast_div_eq (by positivity) h5 h5', ellQ_natCast, lipQ_natCast, zpow_neg,
      zpow_natCast]
    push_cast
    congr 1
    field_simp
    ring

/-- Every row of `constTabA` satisfies `RowConstOK`. -/
theorem constTabA_ok : ∀ e ∈ constTabA, RowConstOK e :=
  fun e he => RowConstOKN.ok ((by decide +kernel : ∀ e ∈ constTabA, RowConstOKN e) e he)

/-- Every row of `constTabB` satisfies `RowConstOK`. -/
theorem constTabB_ok : ∀ e ∈ constTabB, RowConstOK e :=
  fun e he => RowConstOKN.ok ((by decide +kernel : ∀ e ∈ constTabB, RowConstOKN e) e he)

/-- Every row of `constTabC` satisfies `RowConstOK`. -/
theorem constTabC_ok : ∀ e ∈ constTabC, RowConstOK e :=
  fun e he => RowConstOKN.ok ((by decide +kernel : ∀ e ∈ constTabC, RowConstOKN e) e he)

/-- Every row of `constTab` satisfies `RowConstOK`. -/
theorem constTab_ok : ∀ e ∈ constTab, RowConstOK e := by
  intro e he
  simp only [constTab, List.mem_append] at he
  rcases he with (he | he) | he
  · exact constTabA_ok e he
  · exact constTabB_ok e he
  · exact constTabC_ok e he

/-- The certified properties of a table entry `(c, o, p_n, p_d, a_{dir}, a_{jo})`. -/
theorem rowConst_spec {c o pn pd adir ajo : ℕ} (he : (c, o, pn, pd, adir, ajo) ∈ constTab)
    (hc2 : 2 ≤ c) (hc : c ≤ 16) (ho1 : 1 ≤ o) (hoc : o ≤ c) :
    0 < pd ∧ (3 ≤ c → (pn : ℚ) / pd = 1 - c3NarrowDeficit c o) ∧ (c < 3 → pn = pd) ∧
      ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-(o : ℤ))))⌉ = adir ∧
      ⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-(o : ℤ)) +
        9 * c3H17Lip o))⌉ = ajo := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := constTab_ok _ he
  rw [trLipConst_eq_ellQ (by omega) (by omega), c3H17Lip_eq_lipQ (by omega) (by omega)]
  refine ⟨h1, fun h => ?_, h3, h4, h5⟩
  rw [h2 h, c3NarrowDeficit, c3PacketDeficit_eq_c3PacketPotential
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)]

end C3H17Values

end CollatzPosDens
