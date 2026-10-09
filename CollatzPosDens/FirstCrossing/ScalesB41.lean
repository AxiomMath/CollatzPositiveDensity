/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales

/-!
# The scale `b_41 = 233`

The scales `b_j` are given by `b_0 = 9` and `b_{j+1} = b_j + e_{b_j}`. Evaluating this
recursion exactly, with each increment `e_{b_j}` computed from its definition by integer
comparisons, gives `b_41 = 233`. The first terms are `b_0, …, b_6 = 9, 10, 11, 12, 13, 14, 15`.

## Main results

* `CollatzPosDens.scale_41`: `b_41 = 233`.

## Implementation notes

Both `scale` and `eb` are computable natural-number functions with decidable branches, so the
value is obtained by kernel evaluation of the recursion on numerals.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale `b_41` equals `233`. -/
@[collatz_pos_dens "lem_scales_b41"]
theorem scale_41 : scale 41 = 233 := by
  decide +kernel

end CollatzPosDens
