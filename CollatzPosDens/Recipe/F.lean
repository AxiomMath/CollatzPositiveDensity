/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MixingConst

/-!
# The error prefactor `F`

The error prefactor is the positive real number
$$F := 3\,(C + 1),$$
where `C` is the mixing constant `CollatzPosDens.mixingConst`.

## Main definitions

* `CollatzPosDens.errorPrefactor`: the error prefactor `F = 3 (C + 1) ∈ ℝ`.

## Main results

* `CollatzPosDens.errorPrefactor_def`: the defining formula of `F`.
* `CollatzPosDens.errorPrefactor_pos`: `0 < F`.
* `CollatzPosDens.lt_errorPrefactor`, `CollatzPosDens.one_le_errorPrefactor`,
  `CollatzPosDens.mixingConst_lt_errorPrefactor`: the bounds `507/10 < F`, `1 ≤ F` and
  `C < F`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The error prefactor `F := 3 (C + 1) ∈ ℝ`, where `C` is `mixingConst`. -/
@[collatz_pos_dens "def_F"]
noncomputable def errorPrefactor : ℝ := 3 * (mixingConst + 1)

/-- The defining formula of the error prefactor. -/
theorem errorPrefactor_def : errorPrefactor = 3 * (mixingConst + 1) := rfl

/-- The error prefactor exceeds `507/10`. -/
theorem lt_errorPrefactor : 507 / 10 < errorPrefactor := by
  rw [errorPrefactor_def]; linarith [lt_mixingConst]

/-- The error prefactor is positive. -/
theorem errorPrefactor_pos : 0 < errorPrefactor := by
  linarith [lt_errorPrefactor]

/-- The error prefactor is at least `1`. -/
theorem one_le_errorPrefactor : 1 ≤ errorPrefactor := by
  linarith [lt_errorPrefactor]

/-- The mixing constant is less than the error prefactor. -/
theorem mixingConst_lt_errorPrefactor : mixingConst < errorPrefactor := by
  rw [errorPrefactor_def]; linarith [mixingConst_pos]

end CollatzPosDens
