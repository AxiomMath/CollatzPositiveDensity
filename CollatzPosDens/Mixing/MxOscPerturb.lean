/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxAvgContraction
public import CollatzPosDens.Mixing.MxOscSubadditive

/-!
# Perturbation bound for the oscillation

For `m ≤ n` and `c d : ResidueGroup n → ℝ`, the oscillation satisfies
`Osc_{m,n}(c) ≤ Osc_{m,n}(d) + 2 ∑_y |c y - d y|`, the sum running over `ResidueGroup n`.
Writing `c = d + (c - d)`, subadditivity of the oscillation gives
`Osc_{m,n}(c) ≤ Osc_{m,n}(d) + Osc_{m,n}(c - d)`, and the triangle inequality together with the
`ℓ¹` contraction of the fibre average bounds `Osc_{m,n}(c - d)` by `2 ∑_y |c y - d y|`.

## Main results

* `CollatzPosDens.oscillation_le_add_two_mul_sum_abs_sub`: the perturbation bound.

## References

* [Mazur, *Collatz positive density*, §13.3]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Perturbation bound for the oscillation: for `m ≤ n` and `c d : ResidueGroup n → ℝ`,
`Osc_{m,n}(c) ≤ Osc_{m,n}(d) + 2 ∑_y |c y - d y|`, the sum running over `ResidueGroup n`. -/
@[collatz_pos_dens "lem_mx_osc_perturb"]
theorem oscillation_le_add_two_mul_sum_abs_sub {m n : ℕ} (h : m ≤ n)
    (c d : ResidueGroup n → ℝ) :
    oscillation h c ≤ oscillation h d + 2 * ∑ y, |c y - d y| := by
  have hsub := oscillation_sum_le h univ ![d, c - d]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    add_sub_cancel] at hsub
  have hosc :
      oscillation h (c - d) ≤ ∑ y, |c y - d y| + ∑ y, |fiberAvg h (c - d) y| := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun y _ => abs_sub _ _
  have havg : ∑ y, |fiberAvg h (c - d) y| ≤ ∑ y, |c y - d y| :=
    sum_abs_fiberAvg_le h (c - d)
  linarith

end CollatzPosDens
