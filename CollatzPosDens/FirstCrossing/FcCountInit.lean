/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FcSurvivorCount
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Initial surviving counts `c_{b,ℓ_b}(s)`

At the initial length `i = ℓ_b` the only barrier condition in the definition of the surviving
prefix count `c_{b,i}(s)` is `s < H_{b,r_b}(ℓ_b)`, since the only admissible prefix length is
`j = ℓ_b`, for which `x_{≤ j} = x`. The words of `ℤ_{≥1}^ℓ` with sum `s` are the compositions of
`s` into `ℓ` positive parts, of which there are `binom(s-1, ℓ-1)` when `s ≥ ℓ` and none otherwise.
Hence, for `ℓ = ℓ_b ≥ 1`,
`c_{b,ℓ}(s) = binom(s-1, ℓ-1)` if `ℓ ≤ s < H_{b,r_b}(ℓ)`, and `c_{b,ℓ}(s) = 0` otherwise.

## Main results

* `CollatzPosDens.fcSurvivorCount_lb_ncard_words`: the number of words of length `ℓ + 1` and
  valuation sum `n + 1` is `binom(n, ℓ)` (compositions into positive parts).
* `CollatzPosDens.fcSurvivorCount_lb`: the initial surviving counts `c_{b,ℓ_b}(s)`.

## Implementation notes

The statement assumes only `1 ≤ ℓ_b`, which holds for every `b ≥ 1`. The binomial coefficient
`binom(s-1, ℓ-1)` is only used for `s ≥ ℓ ≥ 1`, where it is written with natural-number arguments
`(s.toNat - 1).choose (ℓ - 1)`. The composition count is proved by Pascal's rule: a word of length
`ℓ + 1` and sum `n + 1` either starts with the letter `1`, followed by a word of length `ℓ` and sum
`n`, or starts with a letter `a + 1`, and lowering that letter gives a word of length `ℓ + 1` and
sum `n`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The words of length `ℓ` and valuation sum `n`. -/
private def words (ℓ n : ℕ) : Set Word := {x | x.length = ℓ ∧ x.valSum = n}

private theorem words_succ_succ (ℓ n : ℕ) :
    words (ℓ + 1) (n + 1) = (List.cons 1) '' words ℓ n ∪ Word.incrHead '' words (ℓ + 1) n := by
  ext x
  simp only [words, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hlen, hsum⟩
    rcases x with _ | ⟨a, w⟩
    · simp at hlen
    · rw [Word.valSum_cons] at hsum
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      by_cases ha : a = 1
      · subst ha
        refine Or.inl ⟨w, ⟨hlen, ?_⟩, rfl⟩
        simp at hsum
        omega
      · obtain ⟨k, rfl⟩ := PNat.exists_eq_succ_of_ne_one ha
        refine Or.inr ⟨k :: w, ⟨by simp [hlen], ?_⟩, rfl⟩
        rw [Word.valSum_cons]
        simp only [PNat.add_coe, PNat.val_ofNat] at hsum
        omega
  · rintro (⟨w, ⟨hlen, hsum⟩, rfl⟩ | ⟨y, ⟨hlen, hsum⟩, rfl⟩)
    · refine ⟨by simp [hlen], ?_⟩
      rw [Word.valSum_cons, hsum, PNat.val_ofNat]
      omega
    · rcases y with _ | ⟨a, w⟩
      · simp at hlen
      · refine ⟨by simpa [Word.incrHead] using hlen, ?_⟩
        simp only [Word.incrHead, Word.valSum_cons, PNat.add_coe, PNat.val_ofNat] at hsum ⊢
        omega

private theorem words_succ_zero (ℓ : ℕ) : words (ℓ + 1) 0 = ∅ := by
  ext x
  simp only [words, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hlen hsum
  rw [Word.valSum_eq_zero_iff] at hsum
  simp [hsum] at hlen

private theorem words_finite (ℓ n : ℕ) : (words ℓ n).Finite :=
  (Word.finite_setOf_valSum_le n).subset fun _ hx => hx.2.le

private theorem ncard_words_succ_succ (ℓ n : ℕ) :
    (words (ℓ + 1) (n + 1)).ncard = (words ℓ n).ncard + (words (ℓ + 1) n).ncard := by
  have hdisj : Disjoint ((List.cons 1) '' words ℓ n) (Word.incrHead '' words (ℓ + 1) n) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, -, rfl⟩ ⟨y, -, hy⟩
    rcases y with _ | ⟨a, v⟩
    · simp [Word.incrHead] at hy
    · simp only [Word.incrHead, List.cons.injEq] at hy
      have := congrArg PNat.val hy.1
      simp only [PNat.add_coe, PNat.val_ofNat] at this
      have := a.pos
      omega
  rw [words_succ_succ, Set.ncard_union_eq hdisj ((words_finite _ _).image _)
    ((words_finite _ _).image _), Set.ncard_image_of_injective _ List.cons_injective,
    Set.ncard_image_of_injective _ Word.incrHead_injective]

/-- The number of words `x ∈ ℤ_{≥1}^{ℓ+1}` with valuation sum `n + 1` — compositions of `n + 1`
into `ℓ + 1` positive parts — is `binom(n, ℓ)`. -/
theorem fcSurvivorCount_lb_ncard_words (ℓ n : ℕ) :
    {x : Word | x.length = ℓ + 1 ∧ x.valSum = n + 1}.ncard = n.choose ℓ := by
  change (words (ℓ + 1) (n + 1)).ncard = _
  induction n generalizing ℓ with
  | zero =>
    cases ℓ with
    | zero =>
      have : words 1 1 = {[1]} := by
        ext x
        simp only [words, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hlen, hsum⟩
          rcases x with _ | ⟨a, _ | ⟨c, w⟩⟩
          · simp at hlen
          · simp only [Word.valSum_singleton] at hsum
            simp [PNat.coe_eq_one_iff.1 hsum]
          · simp at hlen
        · rintro rfl
          simp
      simp [this]
    | succ ℓ =>
      rw [ncard_words_succ_succ, words_succ_zero, Set.ncard_empty, zero_add, words_succ_zero]
      simp
  | succ n ih =>
    cases ℓ with
    | zero =>
      rw [ncard_words_succ_succ, ih 0]
      have : words 0 (n + 1) = ∅ := by
        ext x
        simp only [words, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hlen
        simp [List.length_eq_zero_iff.1 hlen, Word.valSum_nil]
      simp [this]
    | succ ℓ =>
      rw [ncard_words_succ_succ, ih ℓ, ih (ℓ + 1), Nat.choose_succ_succ]

private theorem fcSurvivorSet_lb_eq {b ℓ : ℕ} (hℓeq : lb b = ℓ + 1) (n : ℕ) :
    fcSurvivorSet b (lb b) n =
      if (n : ℤ) < barrier b (rb b) (lb b) then words (ℓ + 1) n else ∅ := by
  ext x
  simp only [mem_fcSurvivorSet, words]
  split_ifs with h
  · simp only [Set.mem_ofPred_eq, ← hℓeq, Nat.cast_inj]
    constructor
    · exact fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, by rw [h2], fun j hj1 hj2 => ?_⟩
      obtain rfl : j = lb b := le_antisymm hj2 hj1
      rwa [List.take_of_length_le h1.le, h2]
  · simp only [Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2 h3
    have := h3 (lb b) le_rfl le_rfl
    rw [List.take_of_length_le h1.le, h2] at this
    exact h this

/-- **Initial surviving counts.** For `ℓ = ℓ_b ≥ 1` and every integer `s`,
`c_{b,ℓ}(s) = binom(s-1, ℓ-1)` if `ℓ ≤ s < H_{b,r_b}(ℓ)`, and `c_{b,ℓ}(s) = 0` otherwise. -/
@[collatz_pos_dens "lem_fc_count_init"]
theorem fcSurvivorCount_lb {b : ℕ} (hℓ : 1 ≤ lb b) (s : ℤ) :
    fcSurvivorCount b (lb b) s =
      if (lb b : ℤ) ≤ s ∧ s < barrier b (rb b) (lb b) then (s.toNat - 1).choose (lb b - 1)
      else 0 := by
  rcases lt_or_ge s 0 with hs | hs
  · rw [fcSurvivorCount_of_neg hs, eq_comm, ite_eq_right_iff]
    intro h
    omega
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by omega⟩
  obtain ⟨ℓ, hℓeq⟩ : ∃ ℓ, lb b = ℓ + 1 := ⟨lb b - 1, by omega⟩
  rw [fcSurvivorCount_def, fcSurvivorSet_lb_eq hℓeq, Int.toNat_natCast, hℓeq]
  push_cast
  by_cases h1 : (n : ℤ) < barrier b (rb b) (ℓ + 1)
  · simp only [h1, ↓reduceIte, and_true]
    rcases n with _ | m
    · rw [words_succ_zero, Set.ncard_empty, eq_comm, ite_eq_right_iff]
      intro h
      omega
    · rw [show (words (ℓ + 1) (m + 1)).ncard = _ from fcSurvivorCount_lb_ncard_words ℓ m]
      split_ifs with h2
      · simp
      · exact Nat.choose_eq_zero_of_lt (by omega)
  · simp only [h1, ↓reduceIte, and_false, Set.ncard_empty]

end CollatzPosDens
