/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.OrdinaryTime.S07Bstar
public import CollatzPosDens.OrdinaryTime.CkLateGrowth

/-!
# The generation count is small against the scale sum

For every integer `n ≥ covGen = 23000` the scale sum satisfies
$$2^{22}(n + 1) \le B_*(n).$$
Since `n ≥ 1`, `2^{22}(n + 1) ≤ 2^{23} n ≤ 2^{40} n`; the late growth of the scales gives
`2^{40} n ≤ b_n`; and `b_n ≤ B_*(n) = ∑_{j=0}^{n} b_j`, the scale `b_n` being the summand
`j = n` and every scale being nonnegative.

## Main results

* `CollatzPosDens.two_pow_twentyTwo_mul_succ_le_scaleSum`:
  `2^{22}(n + 1) ≤ B_*(n)` for `n ≥ covGen`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The generation count is small against the scale sum: for every integer `n ≥ covGen`,
`2^{22}(n + 1) ≤ scaleSum n`. -/
@[collatz_pos_dens "lem_ck_count_small"]
theorem two_pow_twentyTwo_mul_succ_le_scaleSum (n : ℕ) (hn : covGen ≤ n) :
    2 ^ 22 * (n + 1) ≤ scaleSum n := by
  have h1 : 1 ≤ n := covGen_pos.trans_le hn
  exact le_trans (by omega) ((two_pow_forty_mul_le_scale n hn).trans (scale_le_scaleSum n))

end CollatzPosDens
