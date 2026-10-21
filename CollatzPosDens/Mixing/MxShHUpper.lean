/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxShHeight
public import CollatzPosDens.Transfer.S03Log3Bounds

/-!
# A linear upper bound on the crossing height of the shell cut

The crossing height `H^{sh}_n = ⌈n log₂ 3⌉` satisfies
$$H^{\mathrm{sh}}_n < n \log_2 3 + 1 \le \frac{317}{200}\, n + 1,$$
using the elementary bound `log₂ 3 < 317 / 200`.

## Main results

* `CollatzPosDens.shHeight_lt_linear`: `H^{sh}_n < (317 / 200) n + 1`.

## Implementation notes

The bound is usually stated for `n ≥ 1`; it holds for every natural number `n`, since
`H^{sh}_0 = 0`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The crossing height of the shell cut grows at most linearly:
`H^{sh}_n < (317 / 200) n + 1`. -/
@[collatz_pos_dens "lem_mx_sh_H_upper"]
theorem shHeight_lt_linear (n : ℕ) : (shHeight n : ℝ) < 317 / 200 * n + 1 := by
  have h := shHeight_lt n
  have hl := logb_two_three_bounds.2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end CollatzPosDens
