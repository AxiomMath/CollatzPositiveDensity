/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3

/-!
# Bounds on `2 ^ ceilLog3 j`

For every `j ∈ ℕ`, the rounded logarithm `ceilLog3 j = ⌈j log₂ 3⌉` satisfies
$$3^j \le 2^{\lceil j \log_2 3 \rceil} \le 2 \cdot 3^j.$$
Indeed `j log₂ 3 ≤ ceilLog3 j < j log₂ 3 + 1`, and exponentiating base `2` gives the claim.

## Main results

* `CollatzPosDens.ceilLog3_bounds`: `3 ^ j ≤ 2 ^ ceilLog3 j ∧ 2 ^ ceilLog3 j ≤ 2 * 3 ^ j`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `j`, `3 ^ j ≤ 2 ^ ceilLog3 j ≤ 2 * 3 ^ j`. -/
@[collatz_pos_dens "lem_s03_ceil_bounds"]
theorem ceilLog3_bounds (j : ℕ) : 3 ^ j ≤ 2 ^ ceilLog3 j ∧ 2 ^ ceilLog3 j ≤ 2 * 3 ^ j :=
  ⟨three_pow_le_two_pow_ceilLog3 j, (two_pow_ceilLog3_lt j).le⟩

end CollatzPosDens
