/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxFiberAvg

/-!
# The fibre average is an `ℓ¹` contraction

For `m ≤ n` and `c : G_n → ℝ`, the fibre average `Avg_{m,n} c` satisfies
`∑_{y ∈ G_n} |Avg_{m,n} c (y)| ≤ ∑_{y ∈ G_n} |c y|`. By the triangle inequality the left side is
at most `3^{m-n} ∑_y ∑_{y' ∼_m y} |c y'|`; exchanging the sums, each `y'` is counted once for
each of the `3^{n-m}` elements `y` of its fibre, which gives `∑_{y'} |c y'|`.

## Main results

* `CollatzPosDens.sum_abs_fiberAvg_le`: `∑_y |Avg_{m,n} c (y)| ≤ ∑_y |c y|`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.3.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The fibre average is an `ℓ¹` contraction: for `m ≤ n` and `c : G_n → ℝ`,
`∑_{y ∈ G_n} |Avg_{m,n} c (y)| ≤ ∑_{y ∈ G_n} |c y|`. -/
@[collatz_pos_dens "lem_mx_avg_contraction"]
theorem sum_abs_fiberAvg_le {m n : ℕ} (h : m ≤ n) (c : ResidueGroup n → ℝ) :
    ∑ y, |fiberAvg h c y| ≤ ∑ y, |c y| := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((m : ℤ) - n) := zpow_pos (by norm_num) _
  calc ∑ y, |fiberAvg h c y|
      ≤ ∑ y, fiberAvg h (fun y' => |c y'|) y := by
        refine sum_le_sum fun y _ => ?_
        rw [fiberAvg, fiberAvg, abs_mul, abs_of_pos hpos]
        exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hpos.le
    _ = ∑ y, |c y| := by
        have := residueAvg_fiberAvg h (fun y' => |c y'|)
        rw [residueAvg_def, residueAvg_def] at this
        exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ (by norm_num))) this

end CollatzPosDens
