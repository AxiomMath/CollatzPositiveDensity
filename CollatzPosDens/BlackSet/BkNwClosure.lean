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
# Triangles are closed under moving north-west

Let `Δ` be a triangle (`CollatzPosDens.BkTriangle`) with corner `(j_Δ, l_Δ)`, and write
`j(q) = bkJ q` and `l(q) = bkL q`. If `q ∈ Δ` and `q'` satisfies `j_Δ ≤ j(q') ≤ j(q)` and
`l(q) ≤ l(q') ≤ l_Δ`, then `q' ∈ Δ`: both terms of the weight
`(j - j_Δ) log 9 + (l_Δ - l) log 2` only decrease when passing from `q` to `q'`.

## Main results

* `CollatzPosDens.BkTriangle.mem_of_mem_of_nw`: a triangle is closed under moving north-west
  inside its corner.

## Implementation notes

No hypothesis `q' ∈ 𝒫` is assumed: `j(q') ≥ j_Δ ≥ 1` already forces it
(`CollatzPosDens.BkTriangle.mem_bkPoints_of_mem`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace BkTriangle

/-- A triangle is closed under moving north-west inside its corner: if `q ∈ Δ`,
`j_Δ ≤ j(q') ≤ j(q)` and `l(q) ≤ l(q') ≤ l_Δ`, then `q' ∈ Δ`. -/
@[collatz_pos_dens "lem_bk_nw_closure"]
theorem mem_of_mem_of_nw {Δ : BkTriangle} {q q' : ℤ × ℤ} (hq : q ∈ Δ)
    (hj₁ : Δ.j ≤ bkJ q') (hj₂ : bkJ q' ≤ bkJ q) (hl₁ : bkL q ≤ bkL q') (hl₂ : bkL q' ≤ Δ.l) :
    q' ∈ Δ := by
  refine ⟨hj₁, hl₂, le_trans ?_ hq.2.2⟩
  have h9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hj : ((bkJ q' - Δ.j : ℤ) : ℝ) ≤ ((bkJ q - Δ.j : ℤ) : ℝ) := by
    exact_mod_cast sub_le_sub_right hj₂ _
  have hl : ((Δ.l - bkL q' : ℤ) : ℝ) ≤ ((Δ.l - bkL q : ℤ) : ℝ) := by
    exact_mod_cast sub_le_sub_left hl₁ _
  exact add_le_add (mul_le_mul_of_nonneg_right hj h9) (mul_le_mul_of_nonneg_right hl h2)

end BkTriangle

end CollatzPosDens
