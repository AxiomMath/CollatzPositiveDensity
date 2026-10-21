/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxShHeight
public import CollatzPosDens.Transfer.S03Log3Bounds

/-!
# A linear lower bound for the crossing height of the shell cut

The crossing height `H^{sh}_n = ⌈n log₂ 3⌉` satisfies
$$\frac{79}{50}\, n \le H^{\mathrm{sh}}_n,$$
since `H^{sh}_n ≥ n log₂ 3` and `log₂ 3 > 79/50`.

## Main results

* `CollatzPosDens.shHeight_lower`: `79/50 · n ≤ H^{sh}_n`.

## Implementation notes

The bound is stated for every natural number `n`, without the hypothesis `n ≥ 1`: both sides
vanish at `n = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The crossing height grows at least linearly: `79/50 · n ≤ H^{sh}_n`. -/
@[collatz_pos_dens "lem_mx_sh_H_lower"]
theorem shHeight_lower (n : ℕ) : (79 / 50 : ℝ) * n ≤ shHeight n := by
  have h := logb_two_three_bounds.1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (79 / 50 : ℝ) * n ≤ n * Real.logb 2 3 := by nlinarith
    _ ≤ shHeight n := le_shHeight n

end CollatzPosDens
