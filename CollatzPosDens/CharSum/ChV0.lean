/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.EpsStar
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum

/-!
# The rational angle `v∘`

The character-sum estimates of the pairing argument compare cosines of the colour angle with
their Taylor polynomials at a fixed rational point below it,
`v∘ = (6283 / 2000) · ε_*`, where `ε_* = 37037 / 10⁶` is the colour scale. Since
`6283 / 2000 < π`, this point lies strictly between `0` and `π ε_*`; being rational, every
polynomial inequality in `v∘` is decided by exact rational arithmetic. Explicitly,
`v∘ = 232703471 / 2000000000`.

## Main definitions

* `CollatzPosDens.chV0`: the rational number `v∘ = (6283 / 2000) · ε_*`.

## Main results

* `CollatzPosDens.chV0_eq_mul`: `v∘ = (6283 / 2000) · ε_*`.
* `CollatzPosDens.chV0_def`: `v∘ = 232703471 / 2000000000`.
* `CollatzPosDens.chV0_pos`: `0 < v∘`.

## Implementation notes

`v∘` is a concrete element of `ℚ`; consumers cast it to `ℝ` where needed. The definition is
exposed, so `norm_num [chV0_def]` evaluates expressions in it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The rational angle `v∘ = (6283 / 2000) · ε_*`. -/
@[collatz_pos_dens "def_ch_v0"]
def chV0 : ℚ := 6283 / 2000 * epsStar

/-- The angle `v∘` is `6283 / 2000` times the colour scale. -/
theorem chV0_eq_mul : chV0 = 6283 / 2000 * epsStar := rfl

/-- The angle `v∘` equals `232703471 / 2000000000`. -/
theorem chV0_def : chV0 = 232703471 / 2000000000 := by
  norm_num [chV0, epsStar]

/-- The angle `v∘` is positive. -/
theorem chV0_pos : 0 < chV0 := by
  rw [chV0_def]; norm_num

end CollatzPosDens
