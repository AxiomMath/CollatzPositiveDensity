/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.OrdinaryTime.Bstar
public import CollatzPosDens.OrdinaryTime.CkLateGrowth

/-!
# A lower bound for the scale sums at late indices

For every integer `n ≥ 2 · 10^{10}` the scale sum satisfies
$$2^{22}(n + 1) \le B_*(n).$$
Since `n ≥ 1`, `2^{22}(n + 1) ≤ 2^{23} n ≤ 2^{40} n`; the late-growth bound of the scales gives
`2^{40} n ≤ b_n`, and `b_n ≤ B_*(n)` because all scales are nonnegative.

## Main results

* `CollatzPosDens.two_pow_twentyTwo_mul_succ_le_scaleSum`:
  `2^{22}(n + 1) ≤ B_*(n)` for `n ≥ 2 · 10^{10}`.

## Implementation notes

The statement is in `ℕ`, where both sides naturally live.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every natural number `n ≥ 2 · 10^{10}`, `2^{22}(n + 1) ≤ B_*(n)`, where `B_*(n)` is
`scaleSum n`. -/
@[collatz_pos_dens "lem_ck_count_small"]
theorem two_pow_twentyTwo_mul_succ_le_scaleSum (n : ℕ) (hn : 2 * 10 ^ 10 ≤ n) :
    2 ^ 22 * (n + 1) ≤ scaleSum n :=
  le_trans (by omega) ((two_pow_forty_mul_le_scale n hn).trans (scale_le_scaleSum n))

end CollatzPosDens
