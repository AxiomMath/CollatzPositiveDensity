/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.PrefixExtension

/-!
# The complement of a prefix-disjoint family

Let `𝒱` be a prefix-disjoint set of words, all of length at most `h`. Then
`1 - 𝐩(𝒱) = 𝐩({v ∈ ℤ_{≥1}^h : no prefix of v lies in 𝒱})`.

The words of length `h` split into the set `E` of those with a prefix in `𝒱` and its complement
`Y`. By `CollatzPosDens.geomMass_eq_geomMass_setOf_prefix_mem`, `𝐩(E) = 𝐩(𝒱)`, and `𝐩` is
additive on the disjoint sets `E`, `Y`, whose union has mass `1`. Hence `𝐩(𝒱) + 𝐩(Y) = 1`, so
`𝐩(𝒱) ≤ 1` is finite and `1 - 𝐩(𝒱) = 𝐩(Y)`.

## Main results

* `CollatzPosDens.geomMass_add_geomMass_setOf_not_prefix_mem`: `𝐩(𝒱) + 𝐩(Y) = 1`.
* `CollatzPosDens.one_sub_geomMass_eq_geomMass_setOf_not_prefix_mem`:
  `1 - 𝐩(𝒱) = 𝐩(Y)`.

## Implementation notes

The mass lives in `ℝ≥0∞`, where subtraction is truncated; since `𝐩(𝒱) ≤ 1` the truncation
never applies, which is the content of the additive form of the identity.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal
open InformationTheory

namespace CollatzPosDens

/-- For a prefix-disjoint family `𝒱` of words of length at most `h`, the mass of `𝒱` and the
mass of the length-`h` words with no prefix in `𝒱` sum to `1`. -/
theorem geomMass_add_geomMass_setOf_not_prefix_mem {V : Set Word} (hV : IsPrefixFree V)
    {h : ℕ} (hlen : ∀ w ∈ V, w.length ≤ h) :
    geomMass V + geomMass {u : Word | u.length = h ∧ ¬ ∃ w ∈ V, w <+: u} = 1 := by
  rw [geomMass_eq_geomMass_setOf_prefix_mem hV hlen, ← geomMass_union, ←
    geomMass_setOf_length_eq h]
  · congr 1
    ext u
    simp only [Set.mem_union, Set.mem_ofPred_eq, ← and_or_left, or_not, and_true]
  · rw [Set.disjoint_left]
    rintro u ⟨_, hu⟩ ⟨_, hu'⟩
    exact hu' hu

/-- **Complement of a prefix-disjoint family.** If `𝒱` is a prefix-disjoint set of words, all of
length at most `h`, then `1 - 𝐩(𝒱) = 𝐩({v ∈ ℤ_{≥1}^h : no prefix of v lies in 𝒱})`. -/
@[collatz_pos_dens "lem_fc_complement"]
theorem one_sub_geomMass_eq_geomMass_setOf_not_prefix_mem {V : Set Word}
    (hV : IsPrefixFree V) {h : ℕ} (hlen : ∀ w ∈ V, w.length ≤ h) :
    1 - geomMass V = geomMass {u : Word | u.length = h ∧ ¬ ∃ w ∈ V, w <+: u} := by
  rw [← geomMass_add_geomMass_setOf_not_prefix_mem hV hlen,
    ENNReal.add_sub_cancel_left (ne_top_of_le_ne_top ENNReal.one_ne_top
      (geomMass_le_one_of_isPrefixFree hV hlen))]

end CollatzPosDens
