/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkTriangle

/-!
# The tip of a triangle

For a triangle `Δ = (j_Δ, l_Δ, s_Δ)`, its *tip* is the real number
`tip(Δ) := l_Δ - s_Δ / log 2`: the (real) second coordinate reached from the corner by spending
the whole size `s_Δ` on steps of weight `log 2` in the `l`-direction.

## Main definitions

* `CollatzPosDens.BkTriangle.tip`: the tip `l_Δ - s_Δ / log 2` of a triangle.

## Main results

* `CollatzPosDens.BkTriangle.l_sub_tip`: `l_Δ - tip(Δ) = s_Δ / log 2`.
* `CollatzPosDens.BkTriangle.tip_le_l_iff`: `tip(Δ) ≤ l_Δ` iff `0 ≤ s_Δ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.2.
-/

@[expose] public section

namespace CollatzPosDens

namespace BkTriangle

/-- The tip `tip(Δ) := l_Δ - s_Δ / log 2` of a triangle `Δ = (j_Δ, l_Δ, s_Δ)`. -/
@[collatz_pos_dens "def_c3_tip"]
noncomputable def tip (Δ : BkTriangle) : ℝ := (Δ.l : ℝ) - Δ.s / Real.log 2

/-- The tip of `Δ` equals `l_Δ - s_Δ / log 2`. -/
theorem tip_def (Δ : BkTriangle) : Δ.tip = (Δ.l : ℝ) - Δ.s / Real.log 2 := rfl

/-- The distance from the corner's `l`-coordinate down to the tip is `s_Δ / log 2`. -/
@[simp]
theorem l_sub_tip (Δ : BkTriangle) : (Δ.l : ℝ) - Δ.tip = Δ.s / Real.log 2 := by
  simp [tip]

/-- The tip lies at or below `l_Δ` exactly when the size is nonnegative. -/
theorem tip_le_l_iff (Δ : BkTriangle) : Δ.tip ≤ Δ.l ↔ 0 ≤ Δ.s := by
  rw [tip_def, sub_le_self_iff, le_div_iff₀ (Real.log_pos one_lt_two), zero_mul]

end BkTriangle

end CollatzPosDens
