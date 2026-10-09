/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockWeight

/-!
# Live block lists

A list `β = (β¹, …, βᵏ)` of blocks is *live* if every block in it has nonzero weight,
`bw(βⁱ) ≠ 0` for `1 ≤ i ≤ k`. Liveness is a property of the multiset of blocks only, so it is
stable under taking prefixes, suffixes and sublists, and a concatenation is live exactly when both
pieces are. Equivalently, a list is live exactly when the product of the weights of its blocks
is nonzero.

## Main definitions

* `CollatzPosDens.TrLive`: the predicate that every block of a list has nonzero weight.

## Main results

* `CollatzPosDens.trLive_nil`, `CollatzPosDens.trLive_cons`,
  `CollatzPosDens.trLive_append`: liveness of the empty list, of `b :: β` and of `β ++ γ`.
* `CollatzPosDens.TrLive.sublist`: a sublist of a live list is live.
* `CollatzPosDens.trLive_iff_prod_ne_zero`: a list is live iff the product of the weights
  of its blocks is nonzero.

## Implementation notes

Lists of blocks of every length occur (`𝔅^q`, `𝔅^k`, `𝔅^N`), so a list in `𝔅^k` is modelled as a
`List (List ℤ × ℤ)` whose length is `k`, and the index `i` with `1 ≤ i ≤ k` becomes membership in
the list. The definition is stated for arbitrary pairs `(c, e)`, not only for those with
`e ∈ {4, 5}`: the block weight makes sense for every pair, and lists in `𝔅^k` are recovered by
restricting the closing letters. No decidability instance is provided: the weights are real
numbers, so `bw(b) ≠ 0` is decidable only classically.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- A list of blocks `β = (β¹, …, βᵏ)` is *live* if `bw(βⁱ) ≠ 0` for every `1 ≤ i ≤ k`. -/
@[collatz_pos_dens "def_tr_live"]
def TrLive (β : List (List ℤ × ℤ)) : Prop :=
  ∀ b ∈ β, chBlockWeight b ≠ 0

/-- A list of blocks `β` is live iff `bw(β[i]) ≠ 0` for every index `i` of `β`. -/
lemma trLive_iff_forall_getElem (β : List (List ℤ × ℤ)) :
    TrLive β ↔ ∀ i : Fin β.length, chBlockWeight β[i] ≠ 0 := by
  simp [TrLive, List.forall_mem_iff_getElem, Fin.forall_iff]

/-- The empty list of blocks is live. -/
@[simp]
lemma trLive_nil : TrLive [] := by simp [TrLive]

/-- The list `b :: β` is live iff `bw(b) ≠ 0` and `β` is live. -/
@[simp]
lemma trLive_cons {b : List ℤ × ℤ} {β : List (List ℤ × ℤ)} :
    TrLive (b :: β) ↔ chBlockWeight b ≠ 0 ∧ TrLive β := by
  simp [TrLive]

/-- The one-block list `[b]` is live iff `bw(b) ≠ 0`. -/
lemma trLive_singleton {b : List ℤ × ℤ} : TrLive [b] ↔ chBlockWeight b ≠ 0 := by
  simp [TrLive]

/-- A concatenation `β ++ γ` is live iff both `β` and `γ` are live. -/
@[simp]
lemma trLive_append {β γ : List (List ℤ × ℤ)} : TrLive (β ++ γ) ↔ TrLive β ∧ TrLive γ := by
  simp [TrLive, or_imp, forall_and]

/-- A list of blocks each of which occurs in a live list is live. -/
lemma TrLive.subset {β γ : List (List ℤ × ℤ)} (h : TrLive γ) (hβ : β ⊆ γ) : TrLive β :=
  fun b hb ↦ h b (hβ hb)

/-- A sublist of a live list of blocks is live. -/
lemma TrLive.sublist {β γ : List (List ℤ × ℤ)} (h : TrLive γ) (hβ : β.Sublist γ) : TrLive β :=
  h.subset hβ.subset

/-- The first `n` blocks of a live list form a live list. -/
lemma TrLive.take {β : List (List ℤ × ℤ)} (h : TrLive β) (n : ℕ) : TrLive (β.take n) :=
  h.sublist (List.take_sublist n β)

/-- Dropping the first `n` blocks of a live list leaves a live list. -/
lemma TrLive.drop {β : List (List ℤ × ℤ)} (h : TrLive β) (n : ℕ) : TrLive (β.drop n) :=
  h.sublist (List.drop_sublist n β)

/-- Every block of a live list has positive weight. -/
lemma TrLive.chBlockWeight_pos {β : List (List ℤ × ℤ)} (h : TrLive β) {b : List ℤ × ℤ}
    (hb : b ∈ β) : 0 < chBlockWeight b :=
  (chBlockWeight_nonneg b).lt_of_ne' (h b hb)

/-- A list of blocks is live iff the product of the weights of its blocks is nonzero. -/
lemma trLive_iff_prod_ne_zero (β : List (List ℤ × ℤ)) :
    TrLive β ↔ (β.map chBlockWeight).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  simp [TrLive]

/-- A list of blocks is live iff the product of the weights of its blocks is positive. -/
lemma trLive_iff_prod_pos (β : List (List ℤ × ℤ)) :
    TrLive β ↔ 0 < (β.map chBlockWeight).prod := by
  refine ⟨fun h ↦ List.prod_pos ?_, fun h ↦ (trLive_iff_prod_ne_zero β).2 h.ne'⟩
  exact List.forall_mem_map.2 fun _ ↦ h.chBlockWeight_pos

end CollatzPosDens
