/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrGap

/-!
# The gap of a black point is nonnegative

For a point `p = (j, l)` the column top `l_*(p)` is at least `l`, so the gap
`gap(p) = l_*(p) - l` is nonnegative.

## Main results

* `CollatzPosDens.trGap_nonneg`: `0 ≤ gap(p)`.

## Implementation notes

The inequality `l ≤ l_*(p)` (`CollatzPosDens.le_bkColTop`) holds for every point and every
colour scale by construction of `l_*`, so the statement carries no hypothesis: `p` need not be
black, and no bound such as `ε_* < 1/4` on the colour scale is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **The gap is nonnegative.** For every point `p` (in particular every black point),
`gap(p) ≥ 0`. -/
@[collatz_pos_dens "lem_tr_gap_nonneg"]
theorem trGap_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    0 ≤ trGap n ξ ε p :=
  sub_nonneg.mpr le_bkColTop

end CollatzPosDens
