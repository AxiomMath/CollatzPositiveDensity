/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxOsc

/-!
# Subadditivity of the oscillation

For `0 ≤ m ≤ n`, a finite index set `I` and functions `c_i : G_n → ℝ`,
`Osc_{m,n}(∑_{i ∈ I} c_i) ≤ ∑_{i ∈ I} Osc_{m,n}(c_i)`.
The fibre average `c ↦ Avg_{m,n} c` is linear, so `∑_i c_i - Avg_{m,n} ∑_i c_i` is pointwise
`∑_i (c_i - Avg_{m,n} c_i)`; the triangle inequality and summation over `y` conclude.

## Main results

* `CollatzPosDens.fiberAvg_sum`: the fibre average commutes with finite sums.
* `CollatzPosDens.oscillation_sum_le`: the oscillation is subadditive over finite sums.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.3.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The fibre average commutes with finite sums:
`Avg_{m,n} (∑_{i ∈ I} c_i) = ∑_{i ∈ I} Avg_{m,n} c_i`. -/
theorem fiberAvg_sum {ι : Type*} {m n : ℕ} (h : m ≤ n) (I : Finset ι)
    (c : ι → ResidueGroup n → ℝ) (y : ResidueGroup n) :
    fiberAvg h (∑ i ∈ I, c i) y = ∑ i ∈ I, fiberAvg h (c i) y := by
  simp only [fiberAvg, Finset.sum_apply, mul_sum]
  rw [sum_comm]

/-- The oscillation is subadditive over finite sums:
`Osc_{m,n}(∑_{i ∈ I} c_i) ≤ ∑_{i ∈ I} Osc_{m,n}(c_i)`. -/
@[collatz_pos_dens "lem_mx_osc_subadditive"]
theorem oscillation_sum_le {ι : Type*} {m n : ℕ} (h : m ≤ n) (I : Finset ι)
    (c : ι → ResidueGroup n → ℝ) :
    oscillation h (∑ i ∈ I, c i) ≤ ∑ i ∈ I, oscillation h (c i) := by
  simp only [oscillation]
  rw [sum_comm]
  refine sum_le_sum fun y _ => ?_
  rw [fiberAvg_sum, Finset.sum_apply, ← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

end CollatzPosDens
