/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.List.Infix

/-!
# Leaves of a policy

A *policy* is a set `W ⊆ ℕ × ℕ × ℕ` of triples `(r, h, c)`: from the state `(r, h)` the letter `c`
is *continued* if `(r, h, c) ∈ W`, and is *terminal* otherwise. Reading an integer word
`λ = (λ₁, …, λₖ)` letter by letter from the state `(r, h)`, the `i`-th letter is read in the
state `(r + i - 1, h + λ₁ + ⋯ + λᵢ₋₁)`. The set `𝔏^W(r, h)` of *leaves* of `W` at `(r, h)` is the
set of the words `λ` with `k ≥ 1` whose letters `λ₁, …, λₖ₋₁` are continued and whose last letter
`λₖ` is terminal, i.e. `(r + i - 1, h + λ₁ + ⋯ + λᵢ₋₁, λᵢ) ∈ W` for `1 ≤ i < k` and
`(r + k - 1, h + λ₁ + ⋯ + λₖ₋₁, λₖ) ∉ W`.

The leaves are the leaves of the decision tree that reads a word letter by letter and stops at
the first terminal letter. In particular `𝔏^W(r, h)` is the disjoint union of the one-letter words
`(c)` with `(r, h, c) ∉ W` and of the words `(c) λ'` with `(r, h, c) ∈ W` and
`λ' ∈ 𝔏^W(r + 1, h + c)`, and it is prefix-free.

## Main definitions

* `CollatzPosDens.PolicyMem`: membership `(r, h, c) ∈ W` of a triple with integer entries `h`, `c`.
* `CollatzPosDens.trTreeLeaves`: the set `𝔏^W(r, h)` of leaves of the policy `W` at `(r, h)`.

## Main results

* `CollatzPosDens.singleton_mem_trTreeLeaves`, `CollatzPosDens.cons_mem_trTreeLeaves`: the
  recursive description of `𝔏^W(r, h)` by the first letter.
* `CollatzPosDens.eq_of_prefix_of_mem_trTreeLeaves`: `𝔏^W(r, h)` is prefix-free, i.e. no leaf is
  a proper prefix of another.

## Implementation notes

The letters of a leaf are integers while `W` consists of triples of natural numbers; a triple
`(r, h, c)` with integer `h`, `c` lies in `W` when it is the image of a member of `W` under the
inclusion `ℕ × ℕ × ℕ → ℕ × ℤ × ℤ` (`CollatzPosDens.PolicyMem`). Letters are indexed from `0`:
the two conditions of the definition are packaged as one equivalence, the `i`-th letter
(`0 ≤ i < k`) being continued exactly when `i + 1 < k`.

## References

* [Mazur, *Collatz positive density*], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- Membership `(r, h, c) ∈ W` of a triple with integer entries `h` and `c` in a set
`W ⊆ ℕ × ℕ × ℕ`: the triple is the image of a member of `W` under `ℕ × ℕ × ℕ → ℕ × ℤ × ℤ`. -/
def PolicyMem (W : Set (ℕ × ℕ × ℕ)) (r : ℕ) (h c : ℤ) : Prop :=
  ∃ n m : ℕ, (r, n, m) ∈ W ∧ (n : ℤ) = h ∧ (m : ℤ) = c

/-- A triple with natural-number entries lies in `W` as an integer triple exactly when it lies in
`W`. -/
@[simp]
lemma policyMem_natCast {W : Set (ℕ × ℕ × ℕ)} {r n m : ℕ} :
    PolicyMem W r n m ↔ (r, n, m) ∈ W := by
  constructor
  · rintro ⟨n', m', h, hn, hm⟩
    rw [Int.natCast_inj.1 hn, Int.natCast_inj.1 hm] at h
    exact h
  · exact fun h => ⟨n, m, h, rfl, rfl⟩

/-- The second entry of a triple of `W` is nonnegative. -/
lemma PolicyMem.nonneg_left {W : Set (ℕ × ℕ × ℕ)} {r : ℕ} {h c : ℤ} (hW : PolicyMem W r h c) :
    0 ≤ h := by
  obtain ⟨n, -, -, rfl, -⟩ := hW
  exact Int.natCast_nonneg n

/-- The third entry of a triple of `W` is nonnegative. -/
lemma PolicyMem.nonneg_right {W : Set (ℕ × ℕ × ℕ)} {r : ℕ} {h c : ℤ} (hW : PolicyMem W r h c) :
    0 ≤ c := by
  obtain ⟨-, m, -, -, rfl⟩ := hW
  exact Int.natCast_nonneg m

/-- The set `𝔏^W(r, h)` of leaves of the policy `W` at the state `(r, h)`: the integer words
`λ = (λ₁, …, λₖ)`, `k ≥ 1`, with `(r + i - 1, h + λ₁ + ⋯ + λᵢ₋₁, λᵢ) ∈ W` for `1 ≤ i < k` and
`(r + k - 1, h + λ₁ + ⋯ + λₖ₋₁, λₖ) ∉ W`. With letters indexed from `0`, the `i`-th letter is
continued exactly when it is not the last one. -/
@[collatz_pos_dens "def_tr_tree_leaves"]
def trTreeLeaves (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) : Set (List ℤ) :=
  {l | l ≠ [] ∧ ∀ (i : ℕ) (hi : i < l.length),
    (PolicyMem W (r + i) (h + (l.take i).sum) l[i] ↔ i + 1 < l.length)}

variable {W : Set (ℕ × ℕ × ℕ)} {r h : ℕ}

/-- The definition of `𝔏^W(r, h)` in the form of two separate conditions on the continued
letters and on the last letter. -/
lemma mem_trTreeLeaves_iff {l : List ℤ} :
    l ∈ trTreeLeaves W r h ↔ ∃ k, ∃ hk : l.length = k + 1,
      (∀ (i : ℕ) (hi : i < k), PolicyMem W (r + i) (h + (l.take i).sum) l[i]) ∧
      ¬ PolicyMem W (r + k) (h + (l.take k).sum) l[k] := by
  constructor
  · rintro ⟨hne, H⟩
    obtain ⟨k, hk⟩ : ∃ k, l.length = k + 1 :=
      Nat.exists_eq_add_one_of_ne_zero (List.length_pos_iff.2 hne).ne'
    exact ⟨k, hk, fun i hi => (H i (by omega)).2 (by omega),
      fun h' => absurd ((H k (by omega)).1 h') (by omega)⟩
  · rintro ⟨k, hk, H, Hk⟩
    refine ⟨List.ne_nil_of_length_pos (by omega), fun i hi => ?_⟩
    rcases Nat.lt_or_ge i k with hik | hik
    · exact iff_of_true (H i hik) (by omega)
    · obtain rfl : i = k := by omega
      exact iff_of_false Hk (by omega)

/-- The empty word is not a leaf. -/
@[simp]
lemma nil_notMem_trTreeLeaves : [] ∉ trTreeLeaves W r h :=
  fun h => h.1 rfl

/-- A leaf is a nonempty word. -/
lemma ne_nil_of_mem_trTreeLeaves {l : List ℤ} (hl : l ∈ trTreeLeaves W r h) : l ≠ [] :=
  hl.1

/-- A one-letter word is a leaf exactly when its letter is terminal. -/
@[simp]
lemma singleton_mem_trTreeLeaves {c : ℤ} :
    [c] ∈ trTreeLeaves W r h ↔ ¬ PolicyMem W r h c := by
  constructor
  · rintro ⟨-, H⟩
    simpa using H 0 (by simp)
  · intro hc
    refine ⟨List.cons_ne_nil _ _, fun i hi => ?_⟩
    obtain rfl : i = 0 := by simpa using hi
    simpa using hc

/-- A word of length at least two is a leaf exactly when its first letter is continued and the
rest of the word is a leaf from the next state. -/
lemma cons_mem_trTreeLeaves {c : ℤ} {l : List ℤ} (hl : l ≠ []) :
    c :: l ∈ trTreeLeaves W r h ↔
      ∃ m : ℕ, (m : ℤ) = c ∧ (r, h, m) ∈ W ∧ l ∈ trTreeLeaves W (r + 1) (h + m) := by
  have hlen : 0 < l.length := List.length_pos_iff.2 hl
  constructor
  · rintro ⟨-, H⟩
    have h0 : PolicyMem W r h c := by
      have := (H 0 (by simp)).2 (by simpa using hlen)
      simp only [List.take_zero, List.sum_nil, add_zero] at this
      exact this
    obtain ⟨n, m, hW, hn, rfl⟩ := h0
    obtain rfl : n = h := Int.natCast_inj.1 hn
    refine ⟨m, rfl, hW, hl, fun i hi => ?_⟩
    have := H (i + 1) (by simpa using hi)
    simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ, List.length_cons,
      Int.natCast_add, ← add_assoc, Nat.add_right_comm r 1 i] at this ⊢
    exact this.trans (by omega)
  · rintro ⟨m, rfl, hW, -, H⟩
    refine ⟨List.cons_ne_nil _ _, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa [hlen] using hW
    · have := H i (by simpa using hi)
      simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ, List.length_cons,
        Int.natCast_add, ← add_assoc, Nat.add_right_comm r 1 i] at this ⊢
      exact this.trans (by omega)

/-- The leaves of `W` at `(r, h)` are the one-letter words `(c)` with `(r, h, c) ∉ W` and the
words `(c) λ'` with `(r, h, c) ∈ W` and `λ' ∈ 𝔏^W(r + 1, h + c)`. -/
lemma mem_trTreeLeaves_cons {c : ℤ} {l : List ℤ} :
    c :: l ∈ trTreeLeaves W r h ↔
      (l = [] ∧ ¬ PolicyMem W r h c) ∨
      ∃ m : ℕ, (m : ℤ) = c ∧ (r, h, m) ∈ W ∧ l ∈ trTreeLeaves W (r + 1) (h + m) := by
  rcases eq_or_ne l [] with rfl | hl
  · simp
  · rw [cons_mem_trTreeLeaves hl]
    simp [hl]

/-- `𝔏^W(r, h)` is prefix-free: a leaf that is a prefix of a leaf is equal to it. -/
lemma eq_of_prefix_of_mem_trTreeLeaves {v w : List ℤ} (hv : v ∈ trTreeLeaves W r h)
    (hw : w ∈ trTreeLeaves W r h) (hvw : v <+: w) : v = w := by
  induction v generalizing r h w with
  | nil => exact absurd hv nil_notMem_trTreeLeaves
  | cons c v ih =>
    obtain ⟨w', rfl⟩ : ∃ w', w = c :: w' := by
      obtain ⟨t, rfl⟩ := hvw
      exact ⟨v ++ t, rfl⟩
    have hvw' : v <+: w' := (List.cons_prefix_cons.1 hvw).2
    rcases eq_or_ne v [] with rfl | hv0
    · rcases eq_or_ne w' [] with rfl | hw0
      · rfl
      · obtain ⟨m, rfl, hW, -⟩ := (cons_mem_trTreeLeaves hw0).1 hw
        exact absurd (policyMem_natCast.2 hW) (singleton_mem_trTreeLeaves.1 hv)
    · obtain ⟨m, rfl, -, hv'⟩ := (cons_mem_trTreeLeaves hv0).1 hv
      have hw0 : w' ≠ [] := by
        rintro rfl
        exact hv0 (List.prefix_nil.1 hvw')
      obtain ⟨m', hm', -, hw'⟩ := (cons_mem_trTreeLeaves hw0).1 hw
      obtain rfl : m' = m := Int.natCast_inj.1 hm'
      rw [ih hv' hw' hvw']

/-- Two leaves of `W` at `(r, h)` that are both prefixes of one word are equal. -/
lemma eq_of_prefix_of_prefix_of_mem_trTreeLeaves {v w z : List ℤ}
    (hv : v ∈ trTreeLeaves W r h) (hw : w ∈ trTreeLeaves W r h) (hvz : v <+: z) (hwz : w <+: z) :
    v = w := by
  rcases List.prefix_or_prefix_of_prefix hvz hwz with hvw | hwv
  · exact eq_of_prefix_of_mem_trTreeLeaves hv hw hvw
  · exact (eq_of_prefix_of_mem_trTreeLeaves hw hv hwv).symm

end CollatzPosDens
