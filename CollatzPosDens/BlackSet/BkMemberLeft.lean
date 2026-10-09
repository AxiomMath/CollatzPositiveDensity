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
# Points of a triangle lie to the left of its right edge

If `q` lies in a triangle `Δ`, then `j(q) ≤ j_Δ + s_Δ / log 9`. Membership `q ∈ Δ` gives
`l(q) ≤ l_Δ` and `(j(q) - j_Δ) log 9 + (l_Δ - l(q)) log 2 ≤ s_Δ`; the second summand is
nonnegative, so `(j(q) - j_Δ) log 9 ≤ s_Δ`.

## Main results

* `CollatzPosDens.BkTriangle.bkJ_le_of_mem`: `j(q) ≤ j_Δ + s_Δ / log 9` for `q ∈ Δ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.4.
-/

@[expose] public section

namespace CollatzPosDens

namespace BkTriangle

/-- A point `q` of a triangle `Δ` satisfies `j(q) ≤ j_Δ + s_Δ / log 9`. -/
@[collatz_pos_dens "lem_bk_member_left"]
theorem bkJ_le_of_mem {Δ : BkTriangle} {q : ℤ × ℤ} (h : q ∈ Δ) :
    (bkJ q : ℝ) ≤ Δ.j + Δ.s / Real.log 9 := by
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : (0 : ℝ) ≤ ((Δ.l - bkL q : ℤ) : ℝ) := by
    exact_mod_cast sub_nonneg.2 (le_l_of_mem h)
  have hw := weight_le_of_mem h
  rw [← sub_le_iff_le_add', le_div_iff₀ hlog9]
  push_cast at hw hl
  nlinarith [mul_nonneg hl hlog2.le]

end BkTriangle

end CollatzPosDens
