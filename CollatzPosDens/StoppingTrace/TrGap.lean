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

Fix a level `n`, a residue `ξ ∈ G_n` and a colour scale `ε`. For a point `p = (j, l)`, if some
integer `t ≥ 1` has `(j, l + t)` white, and `t₀` is the least such `t`, then the *gap* of `p` is
`gap(p) := t₀ - 1 ∈ ℕ`, the number of points of column `j` strictly between `p` and the first
white point above it; if no point `(j, l + t)` with `t ≥ 1` is white, then `gap(p) := 0`.

Writing `l_*(p)` for the top of the run of non-white points of column `j` directly above `p`
(`CollatzPosDens.bkColTop`), both cases say `gap(p) = l_*(p) - l`, and this is how `trGap` is
defined.

## Main definitions

* `CollatzPosDens.trGap n ξ ε p`: the gap `gap(p)`.

## Main results

* `CollatzPosDens.bkColTop_eq_add_trGap`: `l_*(p) = l(p) + gap(p)`.

## Implementation notes

The gap is defined as `(l_*(p) - l).toNat`, so the `Nat.find` API of `CollatzPosDens.bkColTop`
applies to the gap through `bkColTop_eq_add_trGap`. Mazur defines the gap only for black points
and at the colour scale `ε = ε_*` (`CollatzPosDens.epsStar`); here it is defined for every
`p : ℤ × ℤ` and every `ε : ℝ`, and blackness is a hypothesis of the lemmas that need it.

## References

* [Mazur, *Collatz positive density*], §9.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The gap of a point `p = (j, l)`: `l_*(p) - l`, i.e. `t₀ - 1` for the least `t₀ ≥ 1` with
`(j, l + t₀)` white, and `0` if no point `(j, l + t)`, `t ≥ 1`, is white. -/
@[collatz_pos_dens "def_tr_gap"]
noncomputable def trGap (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) : ℕ :=
  (bkColTop n ξ ε p - bkL p).toNat

/-- For every point `p = (j, l)`, in particular every black point, `l_*(p) = l + gap(p)`. -/
@[collatz_pos_dens "lem_tr_gap_top"]
theorem bkColTop_eq_add_trGap (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    bkColTop n ξ ε p = bkL p + trGap n ξ ε p := by
  rw [trGap, Int.toNat_of_nonneg (sub_nonneg.2 le_bkColTop)]
  ring

end CollatzPosDens
