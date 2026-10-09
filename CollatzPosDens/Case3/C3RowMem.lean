/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Case3.C3Row
public import CollatzPosDens.Case3.C3Tip

/-!
# Points below the row of a triangle lie in the triangle

Let `Δ : BkTriangle` and let `l ≤ Δ.l` be an integer height. Every integer `j` with
`Δ.j ≤ j ≤ Δ.row l` gives a point `(j, l)` of `Δ`. Indeed, multiplying
`j - Δ.j ≤ alpha * (l - Δ.tip)` by `log 9` gives
`(j - Δ.j) log 9 ≤ (l - Δ.tip) log 2 = (l - Δ.l) log 2 + Δ.s`, which is the weight condition
of membership.

## Main results

* `CollatzPosDens.BkTriangle.mem_of_le_row`: `(j, l) ∈ Δ` when `l ≤ Δ.l` and
  `Δ.j ≤ j ≤ Δ.row l`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace BkTriangle

/-- If `l ≤ Δ.l` and `Δ.j ≤ j ≤ Δ.row l`, then `(j, l) ∈ Δ`. -/
@[collatz_pos_dens "lem_c3_row_mem"]
theorem mem_of_le_row (Δ : BkTriangle) {l j : ℤ} (hl : l ≤ Δ.l) (hj : Δ.j ≤ j)
    (hrow : (j : ℝ) ≤ Δ.row l) : (j, l) ∈ Δ := by
  refine ⟨hj, hl, ?_⟩
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  rw [row_def, tip_def, alpha_def] at hrow
  have key : ((j : ℝ) - Δ.j) * Real.log 9 ≤ ((l : ℝ) - Δ.l) * Real.log 2 + Δ.s := by
    have := mul_le_mul_of_nonneg_right (sub_le_iff_le_add'.2 hrow) h9.le
    rw [mul_comm (Real.log 2 / Real.log 9), mul_assoc, div_mul_cancel₀ _ h9.ne'] at this
    have e : ((l : ℝ) - (Δ.l - Δ.s / Real.log 2)) * Real.log 2 =
        ((l : ℝ) - Δ.l) * Real.log 2 + Δ.s := by
      field_simp
      ring
    exact e ▸ this
  push_cast
  simp only [bkJ, bkL]
  linarith

end BkTriangle

end CollatzPosDens
