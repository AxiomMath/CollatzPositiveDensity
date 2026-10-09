/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChV0

/-!
# The numerical bound for the fibre of letter `5`

With `v∘ = chV0`, consider the largest of three quantities: the quartic Taylor polynomial
`1 - x² / 4 + x⁴ / 48` of `(1 + cos x) / 2` at `x = 4 v∘`, the constant `3 / 4`, and the
constant `187 / 200`. This file proves that this maximum is strictly below
`1 - 21 / 500 = 479 / 500`.

Since `4 v∘ = 12566 / 27125`, exact rational arithmetic gives
`1 - (4 v∘)² / 4 + (4 v∘)⁴ / 48 = 1538476078510735921 / 1624053164794921875 < 0.94731`,
while `3 / 4 = 0.75` and `187 / 200 = 0.935`.

## Main results

* `CollatzPosDens.ch_fiber5_numeric`: the maximum of the three quantities is `< 1 - 21 / 500`.

## Implementation notes

`v∘` is rational, so the inequality is stated and decided in `ℚ`; its cast to `ℝ` follows by
`Rat.cast_lt` and the cast lemmas for `max`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The quartic Taylor value at `4 v∘`, `3 / 4` and `187 / 200` all lie below `1 - 21 / 500`. -/
@[collatz_pos_dens "lem_ch_fiber5_numeric"]
theorem ch_fiber5_numeric :
    max (1 - (4 * chV0) ^ 2 / 4 + (4 * chV0) ^ 4 / 48) (max (3 / 4) (187 / 200)) <
      (1 - 21 / 500 : ℚ) := by
  norm_num [chV0]

end CollatzPosDens
