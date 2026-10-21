/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShJ
public import CollatzPosDens.Mixing.MxShKhi
public import CollatzPosDens.Mixing.MxShKlo
public import CollatzPosDens.Mixing.MxShSlice
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Retained words of the shell cut

For `n ≥ 1`, the set `R^{sh}_n ⊆ ℤ_{≥1}^n` of *retained words* of the shell cut is the union of
the slices `Sl^{sh}_n(d, j)` over the integers `d, j` with `0 ≤ d ≤ n - 1`,
`k^{sh,-}_n ≤ d ≤ k^{sh,+}_n - 1` and `0 ≤ j ≤ J^{sh}_n`:
$$\mathcal R^{\mathrm{sh}}_n = \bigcup_{d, j} \mathrm{Sl}^{\mathrm{sh}}_n(d, j).$$
The index set is finite; it is recorded as the finset `shRetainedIndex n` of pairs `(d, j)`.

## Main definitions

* `CollatzPosDens.shRetained`: the set `R^{sh}_n` of retained words.
* `CollatzPosDens.shRetainedIndex`: the finite set of indices `(d, j)` of the union.

## Main results

* `CollatzPosDens.mem_shRetained`: the defining membership condition.
* `CollatzPosDens.mxShSlice_subset_shRetained`: each slice of the union lies in `R^{sh}_n`.
* `CollatzPosDens.length_of_mem_shRetained`: retained words have length `n`.
* `CollatzPosDens.mem_shRetainedIndex`: membership in the index set.
* `CollatzPosDens.shRetained_eq_biUnion_shRetainedIndex`: `R^{sh}_n` is the union of the slices
  indexed by `shRetainedIndex n`.
* `CollatzPosDens.shRetained_zero`: `R^{sh}_0 = ∅`.

## Implementation notes

Words are lists of positive integers (`Word`), so `R^{sh}_n` is a `Set Word`; its members all
have length `n`. The definition is stated for `n ≥ 1`; the Lean definition takes every natural
number, and the condition `d ≤ n - 1` is written `d < n`, which agrees with it for `n ≥ 1` and
gives an empty union for `n = 0`. The bounds `k^{sh,±}_n` are integers, so the window condition
is stated after casting `d` to `ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `R^{sh}_n` of *retained words* of the shell cut: the union of the slices
`Sl^{sh}_n(d, j)` over `0 ≤ d ≤ n - 1`, `k^{sh,-}_n ≤ d ≤ k^{sh,+}_n - 1` and
`0 ≤ j ≤ J^{sh}_n`. -/
@[collatz_pos_dens "def_mx_sh_retained"]
def shRetained (n : ℕ) : Set Word :=
  ⋃ (d : ℕ) (j : ℕ) (_ : d < n ∧ shKLo n ≤ d ∧ (d : ℤ) ≤ shKHi n - 1 ∧ j ≤ shJ n),
    mxShSlice n d j

/-- The defining membership condition of `R^{sh}_n`. -/
theorem mem_shRetained {n : ℕ} {w : Word} :
    w ∈ shRetained n ↔ ∃ d j : ℕ,
      (d < n ∧ shKLo n ≤ d ∧ (d : ℤ) ≤ shKHi n - 1 ∧ j ≤ shJ n) ∧ w ∈ mxShSlice n d j := by
  simp only [shRetained, Set.mem_iUnion, exists_prop]

/-- Each slice of the union lies in `R^{sh}_n`. -/
theorem mxShSlice_subset_shRetained {n d j : ℕ} (hdn : d < n) (hlo : shKLo n ≤ d)
    (hhi : (d : ℤ) ≤ shKHi n - 1) (hj : j ≤ shJ n) : mxShSlice n d j ⊆ shRetained n :=
  fun _ hw => mem_shRetained.2 ⟨d, j, ⟨hdn, hlo, hhi, hj⟩, hw⟩

/-- Every retained word has length `n`. -/
theorem length_of_mem_shRetained {n : ℕ} {w : Word} (hw : w ∈ shRetained n) :
    w.length = n := by
  obtain ⟨_, _, _, hw⟩ := mem_shRetained.1 hw
  exact length_of_mem_mxShSlice hw

/-- There are no retained words of length `0`. -/
@[simp]
theorem shRetained_zero : shRetained 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hw => by
    obtain ⟨d, _, ⟨hdn, _⟩, _⟩ := mem_shRetained.1 hw
    omega

/-- The finite set of indices `(d, j)` of the union defining `R^{sh}_n`. -/
noncomputable def shRetainedIndex (n : ℕ) : Finset (ℕ × ℕ) :=
  {x ∈ Finset.range n ×ˢ Finset.range (shJ n + 1) |
    shKLo n ≤ x.1 ∧ (x.1 : ℤ) ≤ shKHi n - 1}

/-- Membership in the index set of `R^{sh}_n`. -/
theorem mem_shRetainedIndex {n d j : ℕ} :
    (d, j) ∈ shRetainedIndex n ↔
      d < n ∧ shKLo n ≤ d ∧ (d : ℤ) ≤ shKHi n - 1 ∧ j ≤ shJ n := by
  simp only [shRetainedIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- `R^{sh}_n` is the union of the slices indexed by the finite set `shRetainedIndex n`. -/
theorem shRetained_eq_biUnion_shRetainedIndex (n : ℕ) :
    shRetained n = ⋃ x ∈ shRetainedIndex n, mxShSlice n x.1 x.2 := by
  ext w
  simp only [mem_shRetained, Set.mem_iUnion, exists_prop, Prod.exists, mem_shRetainedIndex]

end CollatzPosDens
