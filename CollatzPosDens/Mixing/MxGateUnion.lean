/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxSliceGate

/-!
# The union of the slice gates `𝒰_n`

For an integer `n ≥ 1`, the *gate union* is the finite union of the slice gates
$$\mathcal U_n = \bigcup_{k=0}^{n-1} \bigcup_{l=0}^{2n-1} \mathrm{Sl}(n,k,l)
  \subseteq \mathbb{Z}_{\ge 1}^n.$$

## Main definitions

* `CollatzPosDens.mxGateUnion`: the gate union `𝒰_n`, a set of words.

## Main results

* `CollatzPosDens.mem_mxGateUnion`: `w ∈ 𝒰_n` iff `w ∈ Sl(n, k, l)` for some
  `k < n` and `l < 2n`.
* `CollatzPosDens.mxSliceGate_subset_mxGateUnion`: each slice gate with `k < n`,
  `l < 2n` is contained in `𝒰_n`.
* `CollatzPosDens.length_of_mem_mxGateUnion`: members of `𝒰_n` have length `n`.
* `CollatzPosDens.mxGateUnion_eq_biUnion_product`: `𝒰_n` as one union over the index pairs
  `(k, l) ∈ [0, n) × [0, 2n)`.

## Implementation notes

Words are lists of positive integers (`Word`), so `𝒰_n` is a `Set Word`. The index ranges
`0 ≤ k ≤ n - 1` and `0 ≤ l ≤ 2n - 1` are `Finset.range n` and `Finset.range (2 * n)`.
The hypothesis `n ≥ 1` is not needed to form the set (for `n = 0` it is empty).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The gate union `𝒰_n = ⋃_{k < n} ⋃_{l < 2n} Sl(n, k, l)`. -/
@[collatz_pos_dens "def_mx_gate_union"]
noncomputable def mxGateUnion (n : ℕ) : Set Word :=
  ⋃ k ∈ Finset.range n, ⋃ l ∈ Finset.range (2 * n), mxSliceGate n k l

/-- Membership in the gate union `𝒰_n`. -/
theorem mem_mxGateUnion {n : ℕ} {w : Word} :
    w ∈ mxGateUnion n ↔ ∃ k < n, ∃ l < 2 * n, w ∈ mxSliceGate n k l := by
  simp [mxGateUnion]

/-- Each slice gate `Sl(n, k, l)` with `k < n` and `l < 2n` is contained in `𝒰_n`. -/
theorem mxSliceGate_subset_mxGateUnion {n k l : ℕ} (hk : k < n) (hl : l < 2 * n) :
    mxSliceGate n k l ⊆ mxGateUnion n :=
  fun _ hw => mem_mxGateUnion.2 ⟨k, hk, l, hl, hw⟩

/-- Every word of the gate union `𝒰_n` has length `n`. -/
theorem length_of_mem_mxGateUnion {n : ℕ} {w : Word} (hw : w ∈ mxGateUnion n) :
    w.length = n := by
  obtain ⟨k, -, l, -, h⟩ := mem_mxGateUnion.1 hw
  exact length_of_mem_mxSliceGate h

/-- The gate union `𝒰_n` consists of words of length `n`. -/
theorem mxGateUnion_subset_setOf_length (n : ℕ) : mxGateUnion n ⊆ {w : Word | w.length = n} :=
  fun _ hw => length_of_mem_mxGateUnion hw

/-- The gate union as a union over the product index set `[0, n) × [0, 2n)`. -/
theorem mxGateUnion_eq_biUnion_product (n : ℕ) :
    mxGateUnion n = ⋃ p ∈ Finset.range n ×ˢ Finset.range (2 * n), mxSliceGate n p.1 p.2 := by
  ext w
  simp only [mem_mxGateUnion, Set.mem_iUnion, Finset.mem_product, Finset.mem_range, exists_prop,
    Prod.exists]
  constructor
  · rintro ⟨k, hk, l, hl, h⟩
    exact ⟨k, l, ⟨hk, hl⟩, h⟩
  · rintro ⟨k, l, ⟨hk, hl⟩, h⟩
    exact ⟨k, hk, l, hl, h⟩

end CollatzPosDens
