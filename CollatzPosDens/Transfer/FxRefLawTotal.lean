/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RefLaw

/-!
# The reference law has total mass one

The reference weights `μ_n : G_n → [0, ∞]` of `CollatzPosDens.refLaw` form a probability
distribution: `∑_{y ∈ G_n} μ_n(y) = 1` for every `n`. The proof is by induction on `n`. For the
step, exchanging the finite sum over `y ∈ G_{n+1}` with the sum over `a ≥ 1` (all terms are
nonnegative), each `z ∈ G_n` lies in exactly one fibre of the step map
`z ↦ [2^{-a}(3 z̃ + 1)]_{n+1}`, so the total is
`∑_{a ≥ 1} 2^{-a} ∑_z μ_n(z) = ∑_{a ≥ 1} 2^{-a} = 1`.

## Main results

* `CollatzPosDens.sum_refLaw`: `∑_{y ∈ G_n} μ_n(y) = 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- The reference law is a probability distribution: `∑_{y ∈ G_n} μ_n(y) = 1`. -/
@[collatz_pos_dens "lem_fx_ref_law_total"]
theorem sum_refLaw (n : ℕ) : ∑ y, refLaw n y = 1 := by
  induction n with
  | zero => simp [refLaw_zero_apply]
  | succ n ih =>
    simp_rw [refLaw_succ_apply]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [← Finset.mul_sum, Finset.sum_fiberwise, ih, mul_one, pow_succ,
      ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

end CollatzPosDens
