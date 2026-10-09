/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Hold words

For a lattice point `(j, l)` in the set `𝒫 = ℤ_{≥1} × ℤ` of `CollatzPosDens.bkPoints`, the set
of hold words `𝒞_{j,l}` consists of the words `c = (c₁, …, c_j) ∈ ℤ^j` whose letters are all at
least `2`, whose letters before the last avoid `{4, 5}`, whose last letter lies in `{4, 5}`, and
whose letter sum is `l`. Equivalently, the letters are at least `2`, the last letter is the only
one in `{4, 5}`, and the sum is `l`.

## Main definitions

* `CollatzPosDens.holdWords j l`: the set `𝒞_{j,l}` of words `Fin j → ℤ`.

## Main results

* `CollatzPosDens.mem_holdWords_iff`: a word lies in `𝒞_{j,l}` iff its letters are at least
  `2`, exactly its last letter lies in `{4, 5}`, and its letters sum to `l`.
* `CollatzPosDens.holdWords_last_mem`: the last letter of a word in `𝒞_{j+1,l}` lies in
  `{4, 5}`.
* `CollatzPosDens.holdWords_two_mul_add_two_le`: if `𝒞_{j+1,l}` is nonempty then
  `2(j+1) + 2 ≤ l`.

## Implementation notes

A word of length `j` is a function `Fin j → ℤ`, letter `c_i` being `c ⟨i - 1, _⟩`; the
`i`-th letter is the last one iff `i = j`. Mathematically `𝒞_{j,l}` is only considered for
`(j, l) ∈ 𝒫`, that is `j ≥ 1`; here `holdWords` is defined for all `j : ℕ` and `l : ℤ`. For
`j = 0` the conditions on letters are vacuous and `𝒞_{0,l}` is the empty word when `l = 0` and
empty otherwise; this case lies outside `𝒫`.

## References

* [Mazur, §6.1]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The hold words `𝒞_{j,l}`: words `c = (c₁, …, c_j) ∈ ℤ^j` with `c_i ≥ 2` for all `i`,
`c_i ∉ {4, 5}` for `i < j`, `c_j ∈ {4, 5}`, and `c₁ + ⋯ + c_j = l`. -/
@[collatz_pos_dens "def_rn_hold_words"]
def holdWords (j : ℕ) (l : ℤ) : Set (Fin j → ℤ) :=
  {c | (∀ i, 2 ≤ c i) ∧ (∀ i : Fin j, (i : ℕ) + 1 < j → c i ∉ ({4, 5} : Set ℤ)) ∧
    (∀ i : Fin j, (i : ℕ) + 1 = j → c i ∈ ({4, 5} : Set ℤ)) ∧ ∑ i, c i = l}

/-- A word lies in `𝒞_{j,l}` iff its letters are at least `2`, its letters before the last avoid
`{4, 5}`, its last letter lies in `{4, 5}`, and its letters sum to `l`. -/
theorem mem_holdWords {j : ℕ} {l : ℤ} {c : Fin j → ℤ} :
    c ∈ holdWords j l ↔ (∀ i, 2 ≤ c i) ∧
      (∀ i : Fin j, (i : ℕ) + 1 < j → c i ∉ ({4, 5} : Set ℤ)) ∧
      (∀ i : Fin j, (i : ℕ) + 1 = j → c i ∈ ({4, 5} : Set ℤ)) ∧ ∑ i, c i = l :=
  Iff.rfl

/-- A word lies in `𝒞_{j,l}` iff its letters are at least `2`, a letter lies in `{4, 5}` exactly
when it is the last one, and the letters sum to `l`. -/
theorem mem_holdWords_iff {j : ℕ} {l : ℤ} {c : Fin j → ℤ} :
    c ∈ holdWords j l ↔ (∀ i, 2 ≤ c i) ∧
      (∀ i : Fin j, c i ∈ ({4, 5} : Set ℤ) ↔ (i : ℕ) + 1 = j) ∧ ∑ i, c i = l := by
  rw [mem_holdWords]
  refine ⟨fun ⟨h2, hlt, heq, hs⟩ => ⟨h2, fun i => ⟨fun hi => ?_, heq i⟩, hs⟩,
    fun ⟨h2, hiff, hs⟩ => ⟨h2, fun i hi h => hi.ne ((hiff i).1 h),
      fun i hi => (hiff i).2 hi, hs⟩⟩
  by_contra hne
  exact hlt i (by omega) hi

/-- Every letter of a word in `𝒞_{j,l}` is at least `2`. -/
theorem holdWords_two_le {j : ℕ} {l : ℤ} {c : Fin j → ℤ} (hc : c ∈ holdWords j l) (i : Fin j) :
    2 ≤ c i :=
  hc.1 i

/-- The letters of a word in `𝒞_{j,l}` sum to `l`. -/
theorem holdWords_sum_eq {j : ℕ} {l : ℤ} {c : Fin j → ℤ} (hc : c ∈ holdWords j l) :
    ∑ i, c i = l :=
  hc.2.2.2

/-- A letter of a word in `𝒞_{j,l}` other than the last does not lie in `{4, 5}`. -/
theorem holdWords_notMem_of_lt {j : ℕ} {l : ℤ} {c : Fin j → ℤ} (hc : c ∈ holdWords j l)
    (i : Fin j) (hi : (i : ℕ) + 1 < j) : c i ∉ ({4, 5} : Set ℤ) :=
  hc.2.1 i hi

/-- The last letter of a word in `𝒞_{j+1,l}` lies in `{4, 5}`. -/
theorem holdWords_last_mem {j : ℕ} {l : ℤ} {c : Fin (j + 1) → ℤ} (hc : c ∈ holdWords (j + 1) l) :
    c (Fin.last j) ∈ ({4, 5} : Set ℤ) :=
  hc.2.2.1 _ (by simp)

/-- None of the first `j` letters of a word in `𝒞_{j+1,l}` lies in `{4, 5}`. -/
theorem holdWords_castSucc_notMem {j : ℕ} {l : ℤ} {c : Fin (j + 1) → ℤ}
    (hc : c ∈ holdWords (j + 1) l) (i : Fin j) : c i.castSucc ∉ ({4, 5} : Set ℤ) :=
  hc.2.1 _ (by simp)

/-- Membership in `𝒞_{j+1,l}` in terms of the first `j` letters and the last letter. -/
theorem mem_holdWords_succ {j : ℕ} {l : ℤ} {c : Fin (j + 1) → ℤ} :
    c ∈ holdWords (j + 1) l ↔ (∀ i : Fin j, 2 ≤ c i.castSucc ∧ c i.castSucc ∉ ({4, 5} : Set ℤ)) ∧
      c (Fin.last j) ∈ ({4, 5} : Set ℤ) ∧ ∑ i : Fin j, c i.castSucc + c (Fin.last j) = l := by
  rw [mem_holdWords, Fin.sum_univ_castSucc]
  refine ⟨fun ⟨h2, hlt, heq, hs⟩ => ⟨fun i => ⟨h2 _, hlt _ (by simp)⟩, heq _ (by simp), hs⟩,
    fun ⟨hi, hlast, hs⟩ => ⟨fun i => ?_, fun i h => ?_, fun i h => ?_, hs⟩⟩
  · induction i using Fin.lastCases with
    | last => rcases hlast with h | h <;> simp_all
    | cast i => exact (hi i).1
  · induction i using Fin.lastCases with
    | last => simp at h
    | cast i => exact (hi i).2
  · obtain rfl : i = Fin.last j := Fin.ext (by simpa using h)
    exact hlast

/-- A nonempty `𝒞_{j+1,l}` forces `2(j+1) + 2 ≤ l`. -/
theorem holdWords_two_mul_add_two_le {j : ℕ} {l : ℤ} {c : Fin (j + 1) → ℤ}
    (hc : c ∈ holdWords (j + 1) l) : 2 * ((j : ℤ) + 1) + 2 ≤ l := by
  obtain ⟨hi, hlast, hs⟩ := mem_holdWords_succ.1 hc
  have h1 : ∑ _i : Fin j, (2 : ℤ) ≤ ∑ i : Fin j, c i.castSucc :=
    Finset.sum_le_sum fun i _ => (hi i).1
  have h2 : 4 ≤ c (Fin.last j) := by rcases hlast with h | h <;> simp_all
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  linarith

/-- `𝒞_{0,l}` is the empty word if `l = 0`, and empty otherwise. -/
theorem holdWords_zero (l : ℤ) : holdWords 0 l = if l = 0 then Set.univ else ∅ := by
  ext
  split_ifs <;> simp [mem_holdWords, eq_comm, *]

end CollatzPosDens
