/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.InformationTheory.Coding.PrefixFree
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricTotal

/-!
# Extending a prefix-disjoint set of words to a fixed length

Write `𝐩` for the geometric mass `geomMass`, which gives a word `w` the weight
`2^{-A(w)}`, where `A(w) = Word.valSum w` is the sum of its letters. Let `𝒱` be a
prefix-disjoint set of words, all of length at most `h`, and let
`E = {u ∈ ℤ_{≥1}^h : some prefix of u lies in 𝒱}`. Then `𝐩(𝒱) = 𝐩(E)`.

Two prefixes of one word are comparable, so by prefix-disjointness each `u ∈ E` has exactly one
prefix `w ∈ 𝒱`. Hence `E` is the disjoint union over `w ∈ 𝒱` of the blocks
`{w v : v ∈ ℤ_{≥1}^{h - |w|}}`, and since `A(wv) = A(w) + A(v)` the block of `w` has mass
`2^{-A(w)} 𝐩(ℤ_{≥1}^{h-|w|}) = 2^{-A(w)}`.

## Main results

* `CollatzPosDens.geomMass_eq_geomMass_setOf_prefix_mem`: the prefix-extension identity.
* `CollatzPosDens.geomMass_le_one_of_isPrefixFree`: a prefix-free family of bounded length has
  geometric mass at most `1`.
* `CollatzPosDens.isPrefixFree_of_forall_length_eq`: a family of lists of one fixed length is
  prefix-free.

## Implementation notes

Prefix-disjointness is Mathlib's `InformationTheory.IsPrefixFree`. The decomposition of `E` is
the bijection `Σ w ∈ 𝒱, ℤ_{≥1}^{h-|w|} ≃ E`, `(w, v) ↦ w v`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open InformationTheory

namespace CollatzPosDens

/-- Concatenation `(w, v) ↦ w v`, from pairs of a word `w ∈ 𝒱` and a word of length
`h - |w|`, onto the words of length `h` having a prefix in `𝒱`; a bijection when `𝒱` is
prefix-free with all lengths at most `h`. -/
private def prefixExtensionMap (V : Set Word) (h : ℕ) (hlen : ∀ w ∈ V, w.length ≤ h) :
    (Σ w : V, {v : Word | v.length = h - (w : Word).length}) →
      {u : Word | u.length = h ∧ ∃ w ∈ V, w <+: u} :=
  fun p => ⟨(p.1 : Word) ++ p.2.1, by grind [hlen _ p.1.2, p.2.2], p.1, p.1.2,
    List.prefix_append _ _⟩

/-- Concatenation is a bijection onto the words of length `h` with a prefix in `𝒱`: injective
because two prefixes of one word are comparable, surjective by splitting off the prefix. -/
private theorem prefixExtensionMap_bijective {V : Set Word} (hV : IsPrefixFree V) (h : ℕ)
    (hlen : ∀ w ∈ V, w.length ≤ h) : Function.Bijective (prefixExtensionMap V h hlen) := by
  constructor
  · rintro ⟨⟨w₁, hw₁⟩, ⟨v₁, hv₁⟩⟩ ⟨⟨w₂, hw₂⟩, ⟨v₂, hv₂⟩⟩ heq
    simp only [prefixExtensionMap, Subtype.mk.injEq] at heq
    have hp₁ : w₁ <+: w₂ ++ v₂ := heq ▸ List.prefix_append _ _
    have hp₂ : w₂ <+: w₂ ++ v₂ := List.prefix_append _ _
    obtain rfl : w₁ = w₂ := (le_total w₁.length w₂.length).elim
      (fun hl => hV _ hw₁ _ hw₂ (List.prefix_of_prefix_length_le hp₁ hp₂ hl))
      fun hl => (hV _ hw₂ _ hw₁ (List.prefix_of_prefix_length_le hp₂ hp₁ hl)).symm
    cases List.append_cancel_left heq
    rfl
  · rintro ⟨u, hu, w, hw, v, rfl⟩
    exact ⟨⟨⟨w, hw⟩, ⟨v, by grind⟩⟩, rfl⟩

/-- **Prefix extension.** If `𝒱` is a prefix-disjoint set of words, all of length at most `h`,
then `𝐩(𝒱) = 𝐩({u ∈ ℤ_{≥1}^h : some prefix of u lies in 𝒱})`. -/
@[collatz_pos_dens "lem_prefix_extension"]
theorem geomMass_eq_geomMass_setOf_prefix_mem {V : Set Word} (hV : IsPrefixFree V) {h : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ h) :
    geomMass V = geomMass {u : Word | u.length = h ∧ ∃ w ∈ V, w <+: u} := by
  rw [geomMass_def {u : Word | u.length = h ∧ ∃ w ∈ V, w <+: u},
    ← (Equiv.ofBijective _ (prefixExtensionMap_bijective hV h hlen)).tsum_eq,
    ENNReal.tsum_sigma', geomMass_def]
  refine tsum_congr fun w => ?_
  simp only [Equiv.ofBijective_apply, prefixExtensionMap, Word.massWeight, Word.valSum_append,
    pow_add, ENNReal.tsum_mul_left]
  have := geomMass_setOf_length_eq (h - (w : Word).length)
  simp only [geomMass_def, Word.massWeight] at this
  rw [this, mul_one]

/-- A prefix-disjoint set of words of bounded length has geometric mass at most one. -/
theorem geomMass_le_one_of_isPrefixFree {V : Set Word} (hV : IsPrefixFree V) {h : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ h) : geomMass V ≤ 1 := by
  rw [geomMass_eq_geomMass_setOf_prefix_mem hV hlen, ← geomMass_setOf_length_eq h]
  exact geomMass_mono fun u hu => hu.1

/-- A family of lists of one fixed length `t` is prefix-free. -/
theorem isPrefixFree_of_forall_length_eq {α : Type*} {E : Set (List α)} {t : ℕ}
    (hE : ∀ w ∈ E, w.length = t) : IsPrefixFree E :=
  fun _ hx _ hy hxy => hxy.eq_of_length ((hE _ hx).trans (hE _ hy).symm)

end CollatzPosDens
