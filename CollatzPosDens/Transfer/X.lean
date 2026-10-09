/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dstar

/-!
# The scaled threshold `X_*`

The scaled threshold is the rational number
$$X_* := 3200\, D_*,$$
where `D_*` is the renewal threshold `CollatzPosDens.Dstar`.

## Main definitions

* `CollatzPosDens.Xstar`: the scaled threshold `X_* = 3200 D_* ∈ ℚ`.

## Main results

* `CollatzPosDens.Xstar_def`: the defining formula `X_* = 3200 D_*`.
* `CollatzPosDens.cast_Xstar`: the defining formula cast into a division ring of characteristic
  zero, e.g. `ℝ`.
* `CollatzPosDens.Xstar_pos`, `CollatzPosDens.Dstar_le_Xstar`,
  `CollatzPosDens.le_Xstar`: `0 < X_*`, `D_* ≤ X_*` and `6400 ≤ X_*`.

## Implementation notes

`X_*` is defined in `ℚ`, so that exact rational bounds on it can be stated; `cast_Xstar`
transports the defining formula to `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scaled threshold `X_* := 3200 D_* ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_X"]
noncomputable def Xstar : ℚ := 3200 * Dstar

/-- The defining formula of `X_*`. -/
@[simp]
theorem Xstar_def : Xstar = 3200 * Dstar := rfl

/-- The defining formula of `X_*`, cast into a division ring of characteristic zero. -/
theorem cast_Xstar {K : Type*} [DivisionRing K] [CharZero K] :
    (Xstar : K) = 3200 * (Dstar : K) := by
  rw [Xstar_def, Rat.cast_mul, Rat.cast_ofNat]

/-- `X_*` is positive. -/
theorem Xstar_pos : 0 < Xstar := by
  rw [Xstar_def]; exact mul_pos (by norm_num) Dstar_pos

/-- `D_* ≤ X_*`. -/
theorem Dstar_le_Xstar : Dstar ≤ Xstar := by
  rw [Xstar_def]; linarith [Dstar_pos]

/-- `6400 ≤ X_*`. -/
theorem le_Xstar : 6400 ≤ Xstar := by
  rw [Xstar_def]; linarith [two_le_Dstar]

end CollatzPosDens
