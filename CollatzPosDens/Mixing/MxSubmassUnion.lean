/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxSubmass

/-!
# Additivity of the submass over disjoint families

For `n ∈ ℕ`, a finite family `(𝒱_i)_{i ∈ I}` of pairwise disjoint sets of words and a residue
`y ∈ G_n`, the submass is additive:
$$\mathrm{Sub}^n_{\bigcup_{i\in I}\mathcal V_i}(y)=\sum_{i\in I}\mathrm{Sub}^n_{\mathcal V_i}(y).$$
Indeed the fibre of the union over `y` is the disjoint union of the fibres of the `𝒱_i`, and
the geometric mass is additive on disjoint sets.

## Main results

* `CollatzPosDens.subMass_union`: additivity for two disjoint sets.
* `CollatzPosDens.subMass_biUnion_finset`: additivity over a finite pairwise disjoint family.

## Implementation notes

The paper takes `𝒱_i ⊆ ℤ_{≥1}^n`; the statement here holds for arbitrary sets of words, and the
finite index set is a `Finset` of an arbitrary type.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.2.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The submass is additive on two disjoint sets of words. -/
theorem subMass_union (n : ℕ) {U V : Set Word} (h : Disjoint U V) (y : ResidueGroup n) :
    subMass n (U ∪ V) y = subMass n U y + subMass n V y := by
  simp only [subMass_def]
  rw [← geomMass_union]
  · congr 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  · exact Set.disjoint_of_subset (fun _ hw => hw.1) (fun _ hw => hw.1) h

/-- The submass is additive over a finite pairwise disjoint family of sets of words:
`Sub^n_{⋃_{i ∈ I} 𝒱_i}(y) = ∑_{i ∈ I} Sub^n_{𝒱_i}(y)`. -/
@[collatz_pos_dens "lem_mx_submass_union"]
theorem subMass_biUnion_finset (n : ℕ) {ι : Type*} (s : Finset ι) {V : ι → Set Word}
    (hV : (s : Set ι).PairwiseDisjoint V) (y : ResidueGroup n) :
    subMass n (⋃ i ∈ s, V i) y = ∑ i ∈ s, subMass n (V i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [subMass_def, geomMass_empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha, subMass_union,
      ih (hV.subset (by simp))]
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hV (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))

end CollatzPosDens
