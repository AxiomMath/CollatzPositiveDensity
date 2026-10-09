/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Sublists

/-!
# Sublists of block lists

For a list `β = (β¹, …, βᴺ)` and integers `a, b` with `1 ≤ a ≤ b + 1 ≤ N + 1`, the sublist
`β_{[a,b]}` is the contiguous window `(βᵃ, …, βᵇ)`, a list of length `b - a + 1`; it is the empty
list when `b = a - 1`. The two windows of a concatenation `uf` at the cut recover the pieces:
`(uf)_{[1,|u|]} = u` and `(uf)_{[|u|+1,|u|+|f|]} = f`.

## Main definitions

* `CollatzPosDens.trSublist`: the window `β_{[a,b]} = (βᵃ, …, βᵇ)`.

## Main results

* `CollatzPosDens.length_trSublist`: for `b ≤ N`, `β_{[a,b]}` has length `b + 1 - a`.
* `CollatzPosDens.getElem_trSublist`: the `i`-th entry (0-indexed) of `β_{[a,b]}` is
  `β^{a+i}`, i.e. the 0-indexed entry `a - 1 + i` of `β`.
* `CollatzPosDens.trSublist_eq_nil_of_lt`: `β_{[a,a-1]}` is empty.
* `CollatzPosDens.trSublist_append_left`, `CollatzPosDens.trSublist_append_right`:
  `(uf)_{[1,|u|]} = u` and `(uf)_{[|u|+1,|u|+|f|]} = f`.
* `CollatzPosDens.trSublist_append_trSublist`: `β_{[a,b]} β_{[b+1,c]} = β_{[a,c]}`.
* `CollatzPosDens.trSublist_sublist`: `β_{[a,b]}` is a sublist of `β`.

## Implementation notes

The source's `𝔅^N` is modelled by lists (of an arbitrary element type `α`) of length `N`; the
blocks themselves play no role in the definition. The window is `(β.drop (a - 1)).take (b + 1 - a)`
with natural-number indices. Outside the source's range `1 ≤ a ≤ b + 1 ≤ N + 1` this is still
defined (truncated: `b < a - 1` gives the empty list, `b > N` cuts the window at the end of `β`,
and `a = 0` reads as `a = 1`), and the length formula and the entry formula carry the hypotheses
of the source that they need.

## References

* [Mazur, *Collatz positive density*], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

variable {α : Type*}

/-- The sublist `β_{[a,b]} = (βᵃ, …, βᵇ)` of `β = (β¹, …, βᴺ)` (1-indexed), for
`1 ≤ a ≤ b + 1 ≤ N + 1`; it is the empty list when `b = a - 1`. -/
@[collatz_pos_dens "def_tr_sublist"]
def trSublist (β : List α) (a b : ℕ) : List α :=
  (β.drop (a - 1)).take (b + 1 - a)

/-- `β_{[a,b]}` is `(β.drop (a - 1)).take (b + 1 - a)`. -/
lemma trSublist_def (β : List α) (a b : ℕ) :
    trSublist β a b = (β.drop (a - 1)).take (b + 1 - a) := rfl

/-- For `b ≤ N`, the sublist `β_{[a,b]}` lies in `𝔅^{b-a+1}`: it has length `b + 1 - a`. -/
@[simp]
lemma length_trSublist {β : List α} {a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ β.length) :
    (trSublist β a b).length = b + 1 - a := by
  simp [trSublist]; omega

/-- The length of `β_{[a,b]}` in general (truncated at the end of `β`). -/
lemma length_trSublist_eq_min (β : List α) (a b : ℕ) :
    (trSublist β a b).length = min (b + 1 - a) (β.length - (a - 1)) := by
  simp [trSublist]

/-- The entry of `β_{[a,b]}` at 0-indexed position `i` is the entry of `β` at 0-indexed
position `a - 1 + i`, i.e. `β^{a+i}` when `1 ≤ a`. -/
@[simp]
lemma getElem_trSublist {β : List α} {a b i : ℕ} (hi : i < (trSublist β a b).length) :
    (trSublist β a b)[i] =
      β[a - 1 + i]'(by simp [trSublist] at hi; omega) := by
  simp [trSublist]

/-- For `b < a` (in particular `b = a - 1`), `β_{[a,b]}` is the empty list. -/
lemma trSublist_eq_nil_of_lt (β : List α) {a b : ℕ} (hab : b < a) :
    trSublist β a b = [] := by
  simp [trSublist, Nat.sub_eq_zero_of_le hab]

/-- `β_{[1,J]}` is the prefix `(β¹, …, βᴶ)`. -/
@[simp]
lemma trSublist_one (β : List α) (J : ℕ) : trSublist β 1 J = β.take J := by
  simp [trSublist]

/-- `β_{[1,N]} = β`. -/
lemma trSublist_one_length (β : List α) : trSublist β 1 β.length = β := by
  simp

/-- `(uf)_{[1,|u|]} = u`. -/
lemma trSublist_append_left (u f : List α) : trSublist (u ++ f) 1 u.length = u := by
  simp

/-- `(uf)_{[|u|+1,|u|+|f|]} = f`. -/
@[simp]
lemma trSublist_append_right (u f : List α) :
    trSublist (u ++ f) (u.length + 1) (u.length + f.length) = f := by
  simp [trSublist]

/-- Adjacent windows concatenate: `β_{[a,b]} β_{[b+1,c]} = β_{[a,c]}` for
`1 ≤ a ≤ b + 1 ≤ c + 1`. -/
lemma trSublist_append_trSublist (β : List α) {a b c : ℕ} (ha : 1 ≤ a) (hab : a ≤ b + 1)
    (hbc : b ≤ c) : trSublist β a b ++ trSublist β (b + 1) c = trSublist β a c := by
  have h1 : c + 1 - a = (b + 1 - a) + (c + 1 - (b + 1)) := by omega
  have h2 : b + 1 - 1 = (a - 1) + (b + 1 - a) := by omega
  rw [trSublist, trSublist, trSublist, h1, List.take_add, h2, ← List.drop_drop]

/-- `β_{[a,b]}` is a sublist of `β`. -/
lemma trSublist_sublist (β : List α) (a b : ℕ) : (trSublist β a b).Sublist β :=
  (List.take_sublist _ _).trans (List.drop_sublist _ _)

/-- Every entry of `β_{[a,b]}` is an entry of `β`. -/
lemma trSublist_subset (β : List α) (a b : ℕ) : trSublist β a b ⊆ β :=
  (trSublist_sublist β a b).subset

/-- An element of `β_{[a,b]}` is an element of `β`. -/
lemma mem_of_mem_trSublist {β : List α} {a b : ℕ} {x : α} (hx : x ∈ trSublist β a b) : x ∈ β :=
  trSublist_subset β a b hx

/-- Taking a window commutes with mapping: the window `[a,b]` of `β.map g` is the image under `g`
of `β_{[a,b]}`. -/
@[simp]
lemma trSublist_map {γ : Type*} (g : α → γ) (β : List α) (a b : ℕ) :
    trSublist (β.map g) a b = (trSublist β a b).map g := by
  simp [trSublist, List.map_take, List.map_drop]

end CollatzPosDens
