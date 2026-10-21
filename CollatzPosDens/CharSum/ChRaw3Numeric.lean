/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChV0
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# A numerical inequality for the raw three-letter factor

With `v∘ = 232703471 / 2000000000` and `δ = 423871 / 62500000`, the quartic Taylor
polynomial of the cosine at `v∘` lies strictly below the cubic Taylor polynomial of `exp (-δ)`:
`1 - v∘² / 2 + v∘⁴ / 24 < 1 - δ + δ² / 2 - δ³ / 6`.
The left side equals
`381403688860615816410313489118591561281 / 384000000000000000000000000000000000000` and the
right side `1454942884774148334294689 / 1464843750000000000000000`, so this is a statement of
exact rational arithmetic.

## Main results

* `CollatzPosDens.ch_raw3_numeric`: the inequality, in `ℚ`.
* `CollatzPosDens.ch_raw3_numeric_real`: the same inequality after casting to `ℝ`.

## Implementation notes

Since `v∘` is rational, both versions are decided by `norm_num` after rewriting `v∘` to its
value `CollatzPosDens.chV0_def`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `1 - v∘²/2 + v∘⁴/24 < 1 - δ + δ²/2 - δ³/6` with `δ = 423871/62500000`. -/
@[collatz_pos_dens "lem_ch_raw3_numeric"]
theorem ch_raw3_numeric :
    1 - chV0 ^ 2 / 2 + chV0 ^ 4 / 24 <
      1 - 423871 / 62500000 + 1 / 2 * (423871 / 62500000) ^ 2 -
        1 / 6 * (423871 / 62500000 : ℚ) ^ 3 := by
  norm_num [chV0_def]

/-- The inequality `ch_raw3_numeric`, read in `ℝ`. -/
theorem ch_raw3_numeric_real :
    1 - (chV0 : ℝ) ^ 2 / 2 + (chV0 : ℝ) ^ 4 / 24 <
      1 - 423871 / 62500000 + 1 / 2 * (423871 / 62500000) ^ 2 -
        1 / 6 * (423871 / 62500000 : ℝ) ^ 3 := by
  norm_num [chV0_def]

end CollatzPosDens
