/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShPartialSumsBij

/-!
# The exposed pattern of a word

For `N ∈ ℕ` and a word `w`, the *exposed pattern* of `w` is the set of its partial sums lying in
`{1, …, N}`,
$$\mathrm{Ex}_N(w) = \mathrm{Pt}(w) \cap \{1, \dots, N\}.$$
Since the partial sums `S_i = A(w_{≤ i})` are strictly increasing, the indices `i` with
`S_i ≤ N` form an initial segment of `{1, …, |w|}`. Concretely, when some partial sum exceeds
`N`, the word splits as `w = u a r` with `A(u) ≤ N < A(u) + a`, and then `Ex_N(w) = Pt(u)`: the
exposed pattern is the set of partial sums of the longest prefix with valuation sum at most `N`.

## Main definitions

* `CollatzPosDens.Word.exposedPattern`: the exposed pattern `Ex_N(w)`.

## Main results

* `CollatzPosDens.Word.exposedPattern_append_cons`: `Ex_N(u a r) = Pt(u)` when
  `A(u) ≤ N < A(u) + a`.
* `CollatzPosDens.Word.exists_eq_append_cons_of_card_exposedPattern_lt`: if
  `|Ex_N(w)| < |w|`, then `w = u a r` with `A(u) ≤ N < A(u) + a`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

open Finset

/-- The exposed pattern `Ex_N(w) = Pt(w) ∩ {1, …, N}` of a word `w`: its partial sums at
most `N`. -/
@[collatz_pos_dens "def_mx_sh_pattern"]
def exposedPattern (N : ℕ) (w : Word) : Finset ℕ :=
  partialSums w ∩ Icc 1 N

/-- `s ∈ Ex_N(w)` iff `s` is a partial sum of `w` with `s ≤ N`. -/
theorem mem_exposedPattern {N : ℕ} {w : Word} {s : ℕ} :
    s ∈ exposedPattern N w ↔ s ∈ partialSums w ∧ s ≤ N := by
  simp only [exposedPattern, mem_inter, mem_Icc]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, pos_of_mem_partialSums h.1, h.2⟩⟩

/-- The exposed pattern is the set of partial sums at most `N`. -/
theorem exposedPattern_eq_filter (N : ℕ) (w : Word) :
    exposedPattern N w = (partialSums w).filter (· ≤ N) := by
  ext s
  simp [mem_exposedPattern]

/-- `Ex_N(w) ⊆ {1, …, N}`. -/
theorem exposedPattern_subset_Icc (N : ℕ) (w : Word) : exposedPattern N w ⊆ Icc 1 N :=
  inter_subset_right

/-- `Ex_N(w) ⊆ Pt(w)`. -/
theorem exposedPattern_subset_partialSums (N : ℕ) (w : Word) :
    exposedPattern N w ⊆ partialSums w :=
  inter_subset_left

/-- `|Ex_N(w)| ≤ |w|`. -/
theorem card_exposedPattern_le (N : ℕ) (w : Word) : #(exposedPattern N w) ≤ w.length :=
  (card_le_card (exposedPattern_subset_partialSums N w)).trans (card_partialSums w).le

/-- If `A(u) ≤ N < A(u) + a`, the exposed pattern of `u a r` is `Pt(u)`. -/
theorem exposedPattern_append_cons {N : ℕ} {u : Word} {a : ℕ+} (r : Word)
    (hu : valSum u ≤ N) (ha : N < valSum u + a) :
    exposedPattern N (u ++ a :: r) = partialSums u := by
  ext s
  rw [mem_exposedPattern, partialSums_append, mem_union]
  constructor
  · rintro ⟨hs | hs, hsN⟩
    · exact hs
    · obtain ⟨t, ht, rfl⟩ := mem_map.1 hs
      have := le_of_mem_partialSums_cons ht
      simp only [addLeftEmbedding_apply] at hsN
      omega
  · intro hs
    exact ⟨Or.inl hs, (mem_Icc.1 (partialSums_subset_Icc u hs)).2.trans hu⟩

/-- If `A(u) ≤ N < A(u) + a`, then `|Ex_N(u a r)| = |u|`. -/
theorem card_exposedPattern_append_cons {N : ℕ} {u : Word} {a : ℕ+} (r : Word)
    (hu : valSum u ≤ N) (ha : N < valSum u + a) :
    #(exposedPattern N (u ++ a :: r)) = u.length := by
  rw [exposedPattern_append_cons r hu ha, card_partialSums]

/-- A word with a partial sum above `N` splits as `w = u a r` with `A(u) ≤ N < A(u) + a`. -/
theorem exists_eq_append_cons_of_lt_mem_partialSums {N : ℕ} {w : Word} {s : ℕ}
    (hs : s ∈ partialSums w) (hNs : N < s) :
    ∃ (u : Word) (a : ℕ+) (r : Word), w = u ++ a :: r ∧ valSum u ≤ N ∧ N < valSum u + a := by
  induction w generalizing N s with
  | nil => simp at hs
  | cons b w ih =>
    by_cases hb : N < (b : ℕ)
    · exact ⟨[], b, w, rfl, by simp, by simpa using hb⟩
    · rw [partialSums_cons, mem_insert, mem_map] at hs
      rcases hs with rfl | ⟨t, ht, rfl⟩
      · exact absurd hNs hb
      · simp only [addLeftEmbedding_apply] at hNs
        obtain ⟨u, a, r, rfl, hu, ha⟩ := ih (N := N - b) ht (by omega)
        exact ⟨b :: u, a, r, rfl, by simp; omega, by simp; omega⟩

/-- If `|Ex_N(w)| < |w|`, then `w = u a r` with `A(u) ≤ N < A(u) + a`; then `Ex_N(w) = Pt(u)`
by `exposedPattern_append_cons`, so `u` is the prefix of length `|Ex_N(w)|`. -/
theorem exists_eq_append_cons_of_card_exposedPattern_lt {N : ℕ} {w : Word}
    (h : #(exposedPattern N w) < w.length) :
    ∃ (u : Word) (a : ℕ+) (r : Word), w = u ++ a :: r ∧ valSum u ≤ N ∧ N < valSum u + a := by
  obtain ⟨s, hs, hsN⟩ : ∃ s ∈ partialSums w, s ∉ exposedPattern N w := by
    by_contra! hc
    have := card_le_card hc
    rw [card_partialSums] at this
    omega
  exact exists_eq_append_cons_of_lt_mem_partialSums hs
    (not_le.1 fun hle => hsN (mem_exposedPattern.2 ⟨hs, hle⟩))

end Word

end CollatzPosDens
