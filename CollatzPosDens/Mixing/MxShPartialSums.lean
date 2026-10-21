/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Card
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.Maps.Valsum

/-!
# The set of partial sums of a word

For a word `v = (a₁, …, a_d)`, its *set of partial sums* is
$$\mathrm{Pt}(v) = \{A(v_{\le i}) : 1 \le i \le d\} \subseteq \mathbb{Z}_{\ge 1},$$
the set of valuation sums of its nonempty prefixes. Since every letter is a positive integer,
the partial sums `S_i = a₁ + ⋯ + a_i` are strictly increasing, so `Pt(v)` has exactly `d`
elements, all in `{1, …, A(v)}`, and `v` is recovered from `Pt(v)` by taking consecutive
differences.

## Main definitions

* `CollatzPosDens.Word.partialSums`: the set `Pt(v)` of partial sums of a word.

## Main results

* `CollatzPosDens.Word.mem_partialSums`: `s ∈ Pt(v)` iff `s = A(v_{≤ i})` for some
  `1 ≤ i ≤ |v|`.
* `CollatzPosDens.Word.partialSums_cons`: `Pt(a v) = {a} ∪ (a + Pt(v))`.
* `CollatzPosDens.Word.card_partialSums`: `|Pt(v)| = |v|`.
* `CollatzPosDens.Word.partialSums_subset_Icc`: `Pt(v) ⊆ {1, …, A(v)}`.
* `CollatzPosDens.Word.valSum_mem_partialSums`: `A(v) ∈ Pt(v)` for a nonempty word.

## Implementation notes

`Pt(v)` is a `Finset ℕ` rather than a set of positive integers. That its elements are positive
is `CollatzPosDens.Word.zero_notMem_partialSums`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

open Finset

/-- The set of partial sums `Pt(v) = {A(v_{≤ i}) : 1 ≤ i ≤ |v|}` of a word `v`: the valuation
sums of its nonempty prefixes. -/
@[collatz_pos_dens "def_mx_sh_partial_sums"]
def partialSums (v : Word) : Finset ℕ :=
  (Icc 1 v.length).image fun i => valSum (v.take i)

/-- `s ∈ Pt(v)` iff `s = A(v_{≤ i})` for some `1 ≤ i ≤ |v|`. -/
theorem mem_partialSums {v : Word} {s : ℕ} :
    s ∈ partialSums v ↔ ∃ i, 1 ≤ i ∧ i ≤ v.length ∧ valSum (v.take i) = s := by
  simp [partialSums, and_assoc]

/-- The empty word has no partial sums. -/
@[simp]
theorem partialSums_nil : partialSums [] = ∅ := rfl

/-- `Pt(a v) = {a} ∪ (a + Pt(v))`. -/
theorem partialSums_cons (a : ℕ+) (v : Word) :
    partialSums (a :: v) = insert (a : ℕ) ((partialSums v).map (addLeftEmbedding (a : ℕ))) := by
  ext s
  simp only [mem_partialSums, mem_insert, mem_map, addLeftEmbedding_apply, List.length_cons]
  constructor
  · rintro ⟨i, hi1, hi, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · exact Or.inr ⟨_, ⟨j, hj, by omega, rfl⟩, by simp⟩
  · rintro (rfl | ⟨_, ⟨j, hj1, hj, rfl⟩, rfl⟩)
    · exact ⟨1, le_rfl, by omega, by simp⟩
    · exact ⟨j + 1, by omega, by omega, by simp⟩

/-- `Pt([a]) = {a}`. -/
@[simp]
theorem partialSums_singleton (a : ℕ+) : partialSums [a] = {(a : ℕ)} := by
  simp [partialSums_cons]

/-- Every partial sum is positive. -/
theorem pos_of_mem_partialSums {v : Word} {s : ℕ} (hs : s ∈ partialSums v) : 0 < s := by
  obtain ⟨i, hi1, hi, rfl⟩ := mem_partialSums.1 hs
  exact Nat.pos_of_ne_zero fun h => by
    have := List.length_take_of_le hi
    rw [valSum_eq_zero_iff.1 h] at this
    simp at this
    omega

/-- `0 ∉ Pt(v)`. -/
theorem zero_notMem_partialSums (v : Word) : 0 ∉ partialSums v :=
  fun h => (pos_of_mem_partialSums h).ne' rfl

/-- Every partial sum is at most the valuation sum: `Pt(v) ⊆ {1, …, A(v)}`. -/
theorem partialSums_subset_Icc (v : Word) : partialSums v ⊆ Icc 1 (valSum v) := by
  intro s hs
  obtain ⟨i, -, -, rfl⟩ := mem_partialSums.1 hs
  exact mem_Icc.2 ⟨pos_of_mem_partialSums hs,
    valSum_le_of_isPrefix (List.take_prefix i v)⟩

/-- The valuation sum of a nonempty word is one of its partial sums: `A(v) ∈ Pt(v)`. -/
theorem valSum_mem_partialSums {v : Word} (hv : v ≠ []) : valSum v ∈ partialSums v :=
  mem_partialSums.2 ⟨v.length, List.length_pos_iff.2 hv, le_rfl, by simp⟩

/-- A word has as many partial sums as letters: `|Pt(v)| = |v|`. -/
@[simp]
theorem card_partialSums (v : Word) : #(partialSums v) = v.length := by
  induction v with
  | nil => simp
  | cons a v ih =>
    rw [partialSums_cons, card_insert_of_notMem, card_map, ih, List.length_cons]
    simp only [mem_map, addLeftEmbedding_apply, not_exists, not_and]
    intro s hs h
    have := pos_of_mem_partialSums hs
    omega

end Word

end CollatzPosDens
