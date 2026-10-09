/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesB42
public import Mathlib.Logic.Function.Iterate

/-!
# The scale `b_2254`

The scales `b_j` satisfy `b_{2254} ≥ 2^{40}`.

Since the scales are nondecreasing and `b_{42} = 256`, every scale `b_j` with `j ≥ 42` is at
least `256`, so its increment takes the fallback value `e_{b_j} = ⌈b_j/100⌉` and
`b_{j+1} = b_j + ⌈b_j/100⌉`. Iterating this integer recursion `2212` times from `256` gives
`b_{2254} = 1100658881854 > 1099511627776 = 2^{40}`.

## Main results

* `CollatzPosDens.two_pow_forty_le_scale_2254`: `2^{40} ≤ b_{2254}`.
* `CollatzPosDens.scale_2254_eq`: the exact value `b_{2254} = 1100658881854`.

## Implementation notes

The value is obtained by identifying `b_{42+k}` with the `k`-th iterate of
`b ↦ b + (b + 99)/100` at `256` (natural division, equal to `b + ⌈b/100⌉`) and evaluating
the iterate in the kernel on natural-number literals.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value `b_{2254} = 1100658881854`. -/
theorem scale_2254_eq : scale 2254 = 1100658881854 := by
  rw [show (2254 : ℕ) = 42 + 2212 from rfl, scale_42_add]
  decide +kernel

/-- **The scale `b_{2254}`**: `2^{40} ≤ b_{2254}`. -/
@[collatz_pos_dens "lem_ck_scale_2254"]
theorem two_pow_forty_le_scale_2254 : 2 ^ 40 ≤ scale 2254 := by
  rw [scale_2254_eq]
  norm_num

end CollatzPosDens
