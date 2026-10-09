/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChV0

/-!
# The rational `u∘`

Let `v∘ = CollatzPosDens.chV0 = 6283 / 54250`. The cubic Taylor bound `sin v ≥ v - v³ / 6`
evaluated at `v∘` gives a rational lower bound for `sin v∘`; its square
`u∘ = (v∘ - v∘³ / 6)²`
is a rational lower bound for `sin² x` at every angle `x` in `[v∘, π / 2]`.

## Main definitions

* `CollatzPosDens.chU0`: the rational number `u∘ = (v∘ - v∘³ / 6)²`.

## Main results

* `CollatzPosDens.chU0_eq`: the exact value
  `u∘ = 12254388567529692463509142969 / 917700473724336914062500000000`.
* `CollatzPosDens.chV0_sub_cube_pos`: `0 < v∘ - v∘³ / 6`.
* `CollatzPosDens.chU0_pos`: `0 < u∘`.

## Implementation notes

`u∘` is a concrete element of `ℚ`. The definition is exposed, so `norm_num [chU0, chV0]`
decides polynomial inequalities in it; alternatively rewrite with `chU0_eq` first.
-/

@[expose] public section

namespace CollatzPosDens

/-- The rational `u∘ = (v∘ - v∘³ / 6)²`, the square of the cubic Taylor lower bound for
`sin v∘`. -/
@[collatz_pos_dens "def_ch_u0"]
def chU0 : ℚ := (chV0 - chV0 ^ 3 / 6) ^ 2

/-- `u∘` equals `(v∘ - v∘³ / 6)²`. -/
theorem chU0_def : chU0 = (chV0 - chV0 ^ 3 / 6) ^ 2 := rfl

/-- The exact value of `u∘`. -/
theorem chU0_eq : chU0 = 12254388567529692463509142969 / 917700473724336914062500000000 := by
  norm_num [chU0, chV0]

/-- The cubic Taylor lower bound for `sin v∘` is positive. -/
theorem chV0_sub_cube_pos : 0 < chV0 - chV0 ^ 3 / 6 := by
  norm_num [chV0]

/-- The rational `u∘` is positive. -/
theorem chU0_pos : 0 < chU0 := pow_pos chV0_sub_cube_pos 2

/-- The rational `u∘` is nonnegative. -/
theorem chU0_nonneg : 0 ≤ chU0 := chU0_pos.le

end CollatzPosDens
