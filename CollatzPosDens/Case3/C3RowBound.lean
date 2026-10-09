/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Case3.C3Tip

/-!
# Row geometry of triangles

For a triangle `Δ : BkTriangle` with corner `(Δ.j, Δ.l)`, size `Δ.s` and tip
`Δ.tip = Δ.l - Δ.s / log 2`, every point `(j, l) ∈ Δ` satisfies
`(j - Δ.j) log 9 ≤ (l - Δ.tip) log 2`. Membership gives `(j - Δ.j) log 9 ≤ Δ.s - (Δ.l - l) log 2`,
and the right-hand side equals `(l - Δ.tip) log 2`.

## Main results

* `CollatzPosDens.BkTriangle.row_bound_of_mem`: `(j - Δ.j) log 9 ≤ (l - Δ.tip) log 2` for
  `(j, l) ∈ Δ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §10.2.
-/

@[expose] public section

namespace CollatzPosDens

namespace BkTriangle

/-- If `p = (j, l)` lies in the triangle `Δ`, then `(j - Δ.j) log 9 ≤ (l - Δ.tip) log 2`. -/
@[collatz_pos_dens "lem_c3_row_bound"]
theorem row_bound_of_mem {Δ : BkTriangle} {p : ℤ × ℤ} (h : p ∈ Δ) :
    ((bkJ p - Δ.j : ℤ) : ℝ) * Real.log 9 ≤ ((bkL p : ℝ) - Δ.tip) * Real.log 2 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have key : ((bkL p : ℝ) - Δ.tip) * Real.log 2 =
      Δ.s - ((Δ.l - bkL p : ℤ) : ℝ) * Real.log 2 := by
    rw [tip_def]; push_cast; field_simp; ring
  rw [key]
  linarith [weight_le_of_mem h]

end BkTriangle

end CollatzPosDens
