/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShSlice

/-!
# Disjointness of the shell-cut slices

A word `w` of the slice `Sl^{sh}_n(d, j)` has exposed pattern `β = Ex_{H^{sh}_n - 1}(w)` in
`Hd^{sh}_n(d, j)`, so `d = |β|` and `Of(β) ∈ I^{sh}_j`. Both indices are thus determined by `w`:
`d` is the size of its exposed pattern, and `j` is the index of the shell containing the offset
of the pattern, the shells being pairwise disjoint. Hence two slices meet only when their gate
indices `(d, j)` coincide.

## Main results

* `CollatzPosDens.eq_of_mxShSlice_shRetainedHeads_inter_nonempty`: if `Sl^{sh}_n(d, j)` and
  `Sl^{sh}_n(d', j')` meet, then `(d, j) = (d', j')`.
* `CollatzPosDens.disjoint_mxShSlice_shRetainedHeads`: slices of distinct gates are disjoint.

## Implementation notes

The source assumes `n ≥ 1`; the hypothesis is not needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Two shell-cut slices `Sl^{sh}_n(d, j)` and `Sl^{sh}_n(d', j')` meet only when
`(d, j) = (d', j')`. -/
@[collatz_pos_dens "lem_mx_sh_slices_disjoint"]
theorem eq_of_mxShSlice_shRetainedHeads_inter_nonempty {n d d' j j' : ℕ}
    (h : (mxShSlice n d j ∩ mxShSlice n d' j').Nonempty) : (d, j) = (d', j') := by
  obtain ⟨w, hw, hw'⟩ := h
  have hdd : d = d' := (card_exposedPattern_of_mem_mxShSlice hw).symm.trans
    (card_exposedPattern_of_mem_mxShSlice hw')
  subst hdd
  by_contra hne
  have hjj : j ≠ j' := fun h => hne (h ▸ rfl)
  exact Finset.disjoint_left.1 (disjoint_shRetainedHeads n d hjj)
    (exposedPattern_mem_of_mem_mxShSlice hw) (exposedPattern_mem_of_mem_mxShSlice hw')

/-- Shell-cut slices of distinct gates `(d, j) ≠ (d', j')` are disjoint. -/
theorem disjoint_mxShSlice_shRetainedHeads {n d d' j j' : ℕ} (h : (d, j) ≠ (d', j')) :
    Disjoint (mxShSlice n d j) (mxShSlice n d' j') :=
  Set.disjoint_iff_inter_eq_empty.2 <| Set.not_nonempty_iff_eq_empty.1 fun hne =>
    h (eq_of_mxShSlice_shRetainedHeads_inter_nonempty hne)

end CollatzPosDens
