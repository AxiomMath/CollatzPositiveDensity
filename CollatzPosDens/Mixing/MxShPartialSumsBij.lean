/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Function
public import CollatzPosDens.Mixing.MxShPartialSums

/-!
# Partial sums biject words of bounded degree with subsets

For `d, N ∈ ℕ`, the map `v ↦ Pt(v)` sending a word to its set of partial sums is a bijection
from the words `v ∈ ℤ_{≥1}^d` with valuation sum `A(v) ≤ N` onto the `d`-element subsets of
`{1, …, N}`. The partial sums `S_i = A(v_{≤ i})` are strictly increasing, so `Pt(v)` has `d`
elements in `{1, …, A(v)}`; conversely a finite set `{s_1 < ⋯ < s_d}` of positive integers is
`Pt` of the word of consecutive differences `(s_1, s_2 - s_1, …, s_d - s_{d-1})`.

## Main results

* `CollatzPosDens.Word.partialSums_append`: `Pt(uw) = Pt(u) ∪ (A(u) + Pt(w))`.
* `CollatzPosDens.Word.partialSums_injective`: a word is determined by its partial sums.
* `CollatzPosDens.Word.exists_partialSums_eq`: every finite set of positive integers is the set
  of partial sums of some word.
* `CollatzPosDens.Word.bijOn_partialSums`: `Pt` is a bijection from
  `{v : |v| = d, A(v) ≤ N}` onto `{S ⊆ {1, …, N} : |S| = d}`.

## Implementation notes

The injectivity and surjectivity are proved for all words and all finite sets of positive
integers; the length and valuation-sum constraints of the bijection are then read off from
`card_partialSums` and from `A(v) ∈ Pt(v)` (for `v` nonempty), the largest partial sum.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

open Finset

/-- The partial sums of a concatenation: `Pt(uw) = Pt(u) ∪ (A(u) + Pt(w))`. -/
theorem partialSums_append (u w : Word) :
    partialSums (u ++ w) =
      partialSums u ∪ (partialSums w).map (addLeftEmbedding (valSum u)) := by
  induction u with
  | nil => ext; simp
  | cons a u ih =>
    rw [List.cons_append, partialSums_cons, partialSums_cons, ih]
    ext s
    simp only [mem_insert, mem_union, mem_map, addLeftEmbedding_apply, valSum_cons]
    constructor
    · rintro (rfl | ⟨t, ht | ⟨r, hr, rfl⟩, rfl⟩)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
      · exact Or.inr ⟨r, hr, by omega⟩
    · rintro ((rfl | ⟨t, ht, rfl⟩) | ⟨r, hr, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨t, Or.inl ht, rfl⟩
      · exact Or.inr ⟨_, Or.inr ⟨r, hr, rfl⟩, by omega⟩

/-- `Pt(v a) = Pt(v) ∪ {A(v) + a}`. -/
theorem partialSums_append_singleton (v : Word) (a : ℕ+) :
    partialSums (v ++ [a]) = insert (valSum v + a) (partialSums v) := by
  rw [partialSums_append, partialSums_singleton]
  ext s
  simp [or_comm]

/-- Every element of `Pt(a v)` is at least the first letter `a`. -/
theorem le_of_mem_partialSums_cons {a : ℕ+} {v : Word} {s : ℕ}
    (hs : s ∈ partialSums (a :: v)) : (a : ℕ) ≤ s := by
  rw [partialSums_cons, mem_insert, mem_map] at hs
  rcases hs with rfl | ⟨t, -, rfl⟩
  · exact le_rfl
  · simp

/-- A word is determined by its set of partial sums. -/
theorem partialSums_injective : Function.Injective partialSums := by
  intro v
  induction v with
  | nil =>
    intro w h
    have := card_partialSums w
    rw [← h, partialSums_nil, card_empty] at this
    exact (List.eq_nil_of_length_eq_zero this.symm).symm
  | cons a v ih =>
    rintro (_ | ⟨b, w⟩) h
    · have := card_partialSums (a :: v)
      rw [h, partialSums_nil, card_empty] at this
      simp at this
    have hab : a = b := by
      have h₁ : (a : ℕ) ∈ partialSums (b :: w) := h ▸ by simp [partialSums_cons]
      have h₂ : (b : ℕ) ∈ partialSums (a :: v) := h ▸ by simp [partialSums_cons]
      exact PNat.coe_injective
        (le_antisymm (le_of_mem_partialSums_cons h₂) (le_of_mem_partialSums_cons h₁))
    subst hab
    have hnot : ∀ u : Word, (a : ℕ) ∉ (partialSums u).map (addLeftEmbedding (a : ℕ)) := by
      intro u hu
      obtain ⟨t, ht, he⟩ := mem_map.1 hu
      have := pos_of_mem_partialSums ht
      simp only [addLeftEmbedding_apply] at he
      omega
    rw [partialSums_cons, partialSums_cons] at h
    have h' := congrArg (fun S => S.erase (a : ℕ)) h
    simp only [erase_insert (hnot v), erase_insert (hnot w), map_inj] at h'
    rw [ih h']

/-- Every finite set of positive integers is the set of partial sums of some word. -/
theorem exists_partialSums_eq (S : Finset ℕ) (hS : 0 ∉ S) : ∃ v : Word, partialSums v = S := by
  induction S using Finset.induction_on_max with
  | empty => exact ⟨[], rfl⟩
  | insert m S hlt ih =>
    obtain ⟨v, hv⟩ := ih fun h => hS (mem_insert_of_mem h)
    have hm : 0 < m := Nat.pos_of_ne_zero fun h => hS (h ▸ mem_insert_self _ _)
    have hvm : valSum v < m := by
      rcases eq_or_ne v [] with rfl | hne
      · simpa using hm
      · exact hlt _ (hv ▸ valSum_mem_partialSums hne)
    refine ⟨v ++ [Nat.toPNat (m - valSum v) (Nat.sub_pos_of_lt hvm)], ?_⟩
    rw [partialSums_append_singleton, hv]
    exact congrArg (insert · S) (Nat.add_sub_cancel' hvm.le)

/-- **Partial sums biject words of bounded degree with subsets.** For `d, N ∈ ℕ`, the map
`v ↦ Pt(v)` is a bijection from the words of length `d` with valuation sum `A(v) ≤ N` onto the
`d`-element subsets of `{1, …, N}`. -/
@[collatz_pos_dens "lem_mx_sh_partial_sums_bij"]
theorem bijOn_partialSums (d N : ℕ) :
    Set.BijOn partialSums {v : Word | v.length = d ∧ valSum v ≤ N}
      {S : Finset ℕ | S ⊆ Icc 1 N ∧ #S = d} := by
  refine ⟨?_, partialSums_injective.injOn, ?_⟩
  · rintro v ⟨hd, hN⟩
    exact ⟨(partialSums_subset_Icc v).trans (Icc_subset_Icc le_rfl hN),
      (card_partialSums v).trans hd⟩
  · rintro S ⟨hS, hd⟩
    obtain ⟨v, rfl⟩ := exists_partialSums_eq S fun h => by simpa using hS h
    refine ⟨v, ⟨(card_partialSums v).symm.trans hd, ?_⟩, rfl⟩
    rcases eq_or_ne v [] with rfl | hne
    · exact Nat.zero_le _
    · exact (mem_Icc.1 (hS (valSum_mem_partialSums hne))).2

end Word

end CollatzPosDens
