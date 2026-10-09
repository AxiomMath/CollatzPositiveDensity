/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Case3.C3Tip

/-!
# The row of a triangle

For a triangle `Δ` and an integer `l*`, the *row* of `Δ` at `l*` is the real number
`row_Δ(l*) := j_Δ + α (l* - tip(Δ))`, where `α = log 2 / log 9` is the slope of the black set
and `tip(Δ) = l_Δ - s_Δ / log 2`. It is an affine function of `l*` of slope `α`, taking the value
`j_Δ` at the (real) height `tip(Δ)`.

## Main definitions

* `CollatzPosDens.BkTriangle.row`: the row `j_Δ + α (l* - tip(Δ))`.

## Main results

* `CollatzPosDens.BkTriangle.row_sub_row`: `row_Δ(l) - row_Δ(l') = α (l - l')`.
* `CollatzPosDens.BkTriangle.row_strictMono`: `row_Δ` is strictly increasing.
* `CollatzPosDens.BkTriangle.row_le_row_iff`, `CollatzPosDens.BkTriangle.row_lt_row_iff`:
  rows compare as their heights do.
* `CollatzPosDens.BkTriangle.row_l`: `row_Δ(l_Δ) = j_Δ + s_Δ / log 9`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.2.
-/

@[expose] public section

namespace CollatzPosDens

namespace BkTriangle

/-- The row `row_Δ(l*) := j_Δ + α (l* - tip(Δ))` of a triangle `Δ` at height `l* ∈ ℤ`. -/
@[collatz_pos_dens "def_c3_row"]
noncomputable def row (Δ : BkTriangle) (l : ℤ) : ℝ := (Δ.j : ℝ) + alpha * ((l : ℝ) - Δ.tip)

/-- The row of `Δ` at `l` equals `j_Δ + α (l - tip(Δ))`. -/
theorem row_def (Δ : BkTriangle) (l : ℤ) : Δ.row l = (Δ.j : ℝ) + alpha * ((l : ℝ) - Δ.tip) :=
  rfl

/-- The row is affine of slope `α`. -/
theorem row_sub_row (Δ : BkTriangle) (l l' : ℤ) :
    Δ.row l - Δ.row l' = alpha * ((l : ℝ) - l') := by
  simp only [row_def]
  ring

/-- The row is strictly increasing in the height. -/
theorem row_strictMono (Δ : BkTriangle) : StrictMono Δ.row := fun l l' h => by
  have := row_sub_row Δ l' l
  have : (0 : ℝ) < alpha * ((l' : ℝ) - l) :=
    mul_pos alpha_pos (sub_pos.2 (Int.cast_lt.2 h))
  linarith

/-- `row_Δ(l) ≤ row_Δ(l')` if and only if `l ≤ l'`. -/
@[simp]
theorem row_le_row_iff (Δ : BkTriangle) {l l' : ℤ} : Δ.row l ≤ Δ.row l' ↔ l ≤ l' :=
  Δ.row_strictMono.le_iff_le

/-- `row_Δ(l) < row_Δ(l')` if and only if `l < l'`. -/
@[simp]
theorem row_lt_row_iff (Δ : BkTriangle) {l l' : ℤ} : Δ.row l < Δ.row l' ↔ l < l' :=
  Δ.row_strictMono.lt_iff_lt

/-- At the corner height `l_Δ`, the row is `j_Δ + s_Δ / log 9`. -/
theorem row_l (Δ : BkTriangle) : Δ.row Δ.l = (Δ.j : ℝ) + Δ.s / Real.log 9 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [row_def, l_sub_tip, alpha_def]
  field_simp

end BkTriangle

end CollatzPosDens
