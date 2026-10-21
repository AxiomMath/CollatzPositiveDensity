/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.Transfer.EpsStar

/-!
# The gap of a black point

Fix a level `n`, a residue `ξ ∈ G_n` and a colour scale `ε`. For a point `p = (j, l)` write
`l_*(p)` for the top of the run of non-white points of column `j` directly above `p`
(`CollatzPosDens.bkColTop`). The *gap* of `p` is the integer `gap(p) := l_*(p) - l(p)`, the
vertical distance from `p` to the top of its column run.

## Main definitions

* `CollatzPosDens.trGap n ξ ε p`: the gap `gap(p) = l_*(p) - l(p) ∈ ℤ`.

## Main results

* `CollatzPosDens.bkColTop_eq_add_trGap`: `l_*(p) = l(p) + gap(p)`.

## Implementation notes

The gap is defined for every `p : ℤ × ℤ`, not only for black points, and blackness is a
hypothesis of the lemmas that need it. The definition is stated for an arbitrary colour scale
`ε : ℝ`; it is applied at `ε = ε_*` (`CollatzPosDens.epsStar`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The gap of a point `p = (j, l)`: the integer `l_*(p) - l`, the distance from `p` to the top
of the run of non-white points of its column directly above it. -/
@[collatz_pos_dens "def_tr_gap"]
noncomputable def trGap (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : ℤ :=
  bkColTop n ξ ε p - bkL p

/-- For every point `p = (j, l)`, `l_*(p) = l + gap(p)`. -/
theorem bkColTop_eq_add_trGap (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    bkColTop n ξ ε p = bkL p + trGap n ξ ε p :=
  (add_sub_cancel _ _).symm

end CollatzPosDens
