/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.D1
public import CollatzPosDens.Transfer.Dpt
public import CollatzPosDens.Transfer.Dexp
public import CollatzPosDens.Transfer.Dbad
public import CollatzPosDens.Transfer.Dsc
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.Order

/-!
# The renewal threshold `D_*`

The renewal threshold is the rational number
$$D_* := \max\bigl(D_1,\ D_{\mathrm{pt}},\ D_{\exp},\ D_{\mathrm{bad}},\ D_{\mathrm{sc}},\
  1,\ 2\bigr),$$
the maximum of the exit threshold `D_1`, the point threshold `D_pt`, the moment threshold
`D_exp`, the bad-advance threshold `D_bad`, the scale threshold `D_sc`, and the numbers `1`
and `2`. It dominates each of these thresholds.

## Main definitions

* `CollatzPosDens.Dstar`: the renewal threshold `D_* ∈ ℚ`.

## Main results

* `CollatzPosDens.Dstar_def`: the defining formula of `D_*`.
* `CollatzPosDens.cast_Dstar`: the defining formula cast into a linearly ordered field of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.D1_le_Dstar`, `CollatzPosDens.Dpt_le_Dstar`,
  `CollatzPosDens.Dexp_le_Dstar`, `CollatzPosDens.Dbad_le_Dstar`,
  `CollatzPosDens.Dsc_le_Dstar`, `CollatzPosDens.one_le_Dstar`,
  `CollatzPosDens.two_le_Dstar`: each entry of the maximum is at most `D_*`.
* `CollatzPosDens.Dstar_le_iff`: a characterisation of upper bounds for `D_*`.
* `CollatzPosDens.Dstar_pos`: `0 < D_*`.

## Implementation notes

The natural-number thresholds `D_exp` and `D_sc` enter through their casts to `ℚ`. The
maximum of seven numbers is the left-nested binary maximum. Since `D_exp`, `D_bad` and `D_sc`
are numbers with thousands of digits, `D_*` is irreducible and is used only through the lemmas
of this file, never by evaluation.
-/

@[expose] public section

namespace CollatzPosDens

/-- The renewal threshold `D_* := max (D_1, D_pt, D_exp, D_bad, D_sc, 1, 2) ∈ ℚ`. -/
@[collatz_pos_dens "def_Dstar", irreducible]
noncomputable def Dstar : ℚ :=
  max (max (max (max (max (max D1 Dpt) (Dexp : ℚ)) Dbad) (Dsc : ℚ)) 1) 2

/-- The defining formula of `D_*`. -/
theorem Dstar_def :
    Dstar = max (max (max (max (max (max D1 Dpt) (Dexp : ℚ)) Dbad) (Dsc : ℚ)) 1) 2 := by
  unfold Dstar; rfl

/-- A rational number bounds `D_*` from above iff it bounds every entry of the maximum. -/
theorem Dstar_le_iff {x : ℚ} :
    Dstar ≤ x ↔ D1 ≤ x ∧ Dpt ≤ x ∧ (Dexp : ℚ) ≤ x ∧ Dbad ≤ x ∧ (Dsc : ℚ) ≤ x ∧ 1 ≤ x ∧
      2 ≤ x := by
  simp only [Dstar_def, max_le_iff, and_assoc]

/-- The defining formula of `D_*`, cast into a linearly ordered field of characteristic zero. -/
theorem cast_Dstar {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (Dstar : K) = max (max (max (max (max (max (D1 : K) (Dpt : K)) (Dexp : K)) (Dbad : K))
      (Dsc : K)) 1) 2 := by
  rw [Dstar_def]; push_cast; rfl

/-- `D_1 ≤ D_*`. -/
theorem D1_le_Dstar : D1 ≤ Dstar := by
  rw [Dstar_def]; simp only [le_max_iff, le_refl, true_or]

/-- `D_pt ≤ D_*`. -/
theorem Dpt_le_Dstar : Dpt ≤ Dstar := by
  rw [Dstar_def]; simp only [le_max_iff, le_refl, true_or, or_true]

/-- `D_exp ≤ D_*`. -/
theorem Dexp_le_Dstar : (Dexp : ℚ) ≤ Dstar := by
  rw [Dstar_def]; simp only [le_max_iff, le_refl, true_or, or_true]

/-- `D_bad ≤ D_*`. -/
theorem Dbad_le_Dstar : Dbad ≤ Dstar := by
  rw [Dstar_def]; simp only [le_max_iff, le_refl, true_or, or_true]

/-- `D_sc ≤ D_*`. -/
theorem Dsc_le_Dstar : (Dsc : ℚ) ≤ Dstar := by
  rw [Dstar_def]; simp only [le_max_iff, le_refl, true_or, or_true]

/-- `2 ≤ D_*`. -/
theorem two_le_Dstar : 2 ≤ Dstar := by
  rw [Dstar_def]; exact le_max_right _ _

/-- `1 ≤ D_*`. -/
theorem one_le_Dstar : 1 ≤ Dstar := one_le_two.trans two_le_Dstar

/-- `D_*` is positive. -/
theorem Dstar_pos : 0 < Dstar := lt_of_lt_of_le two_pos two_le_Dstar

end CollatzPosDens
