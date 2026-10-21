/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShGate
public import CollatzPosDens.Mixing.MxShHeadMeasure
public import CollatzPosDens.Mixing.MxShGateSup

/-!
# Collision bound for a gate

For `n ≥ 1` and `d j : ℕ`, the squares of the head measure `shHeadMeasure n d j` over the
residue group `ResidueGroup n` satisfy
```
3 ^ n * ∑ y, shHeadMeasure n d j y ^ 2 ≤
  (shShellWidth j + 2) * (2 ^ (shHeight n - 1))⁻¹ * #(shRetainedHeads n d j).
```

The supremum bound `pow_three_mul_shHeadMeasure_lt` gives
`3 ^ n * shHeadMeasure n d j y ^ 2 ≤ (shShellWidth j + 2) * shHeadMeasure n d j y`, and summing
over `y` with `sum_shHeadMeasure`, which counts each retained head at exactly one residue, gives
the bound.

## Main results

* `CollatzPosDens.pow_three_mul_sum_shHeadMeasure_sq_le`: the collision bound above.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- **Collision bound for a gate.** For `n ≥ 1`, three to the `n` times the sum over the residue
group of the squared head measure `shHeadMeasure n d j` is at most `shShellWidth j + 2` times
`(2 ^ (shHeight n - 1))⁻¹` times the number of retained heads `shRetainedHeads n d j`. -/
@[collatz_pos_dens "lem_mx_sh_gate_square"]
theorem pow_three_mul_sum_shHeadMeasure_sq_le {n : ℕ} (hn : 1 ≤ n) (d j : ℕ) :
    3 ^ n * ∑ y : ResidueGroup n, shHeadMeasure n d j y ^ 2 ≤
      (shShellWidth j + 2) * ((2 : ℚ) ^ (shHeight n - 1))⁻¹ * #(shRetainedHeads n d j) := by
  rw [mul_assoc, ← sum_shHeadMeasure, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [sq, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_three_mul_shHeadMeasure_lt hn d j y).le
    (shHeadMeasure_nonneg n d j y)

end CollatzPosDens
