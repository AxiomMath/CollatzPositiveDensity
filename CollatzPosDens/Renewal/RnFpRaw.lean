/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Raw first-passage words

For `s ∈ ℕ`, `r ≥ 1` and `ℓ ∈ ℤ`, the set of raw first-passage words `𝒟_s(r, ℓ)` consists of the
words `c = (c₁, …, c_r) ∈ ℤ^r` whose letters are all at least `2`, whose last letter lies in
`{4, 5}`, whose letters sum to `ℓ`, and such that every earlier letter lying in `{4, 5}` ends a
prefix of sum at most `s`: `c₁ + ⋯ + c_i ≤ s` for every `i < r` with `c_i ∈ {4, 5}`.

Since the letters are at least `2` and sum to `ℓ`, each letter lies in `[2, ℓ]`, so `𝒟_s(r, ℓ)` is
finite; it is defined here as a `Finset`, so that sums over it make sense.

## Main definitions

* `CollatzPosDens.firstPassageWords s r ℓ`: the finite set `𝒟_s(r, ℓ)` of words `Fin r → ℤ`.

## Main results

* `CollatzPosDens.mem_firstPassageWords`: membership in `𝒟_s(r, ℓ)` is exactly the four
  conditions of the definition.
* `CollatzPosDens.firstPassageWords_last_mem`: the last letter of a word in `𝒟_s(r+1, ℓ)`
  lies in `{4, 5}`.

## Implementation notes

A word of length `r` is a function `Fin r → ℤ`, letter `c_i` being `c ⟨i - 1, _⟩`; the prefix sum
`c₁ + ⋯ + c_i` is `∑ j ∈ Iic ⟨i - 1, _⟩, c j`. In [mazur2026] the set `𝒟_s(r, ℓ)` is defined
only for `r ≥ 1`; here `r` is any natural number, the condition on the last letter being stated as
"the letter of index `r` lies in `{4, 5}`". For `r = 0` this is vacuous, so `𝒟_s(0, ℓ)` consists
of the empty word when `ℓ = 0` and is empty otherwise.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.4
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The raw first-passage words `𝒟_s(r, ℓ)`: words `c = (c₁, …, c_r) ∈ ℤ^r` with `c_i ≥ 2` for all
`i`, `c_r ∈ {4, 5}`, `c₁ + ⋯ + c_r = ℓ`, and `c₁ + ⋯ + c_i ≤ s` for every `i < r` with
`c_i ∈ {4, 5}`. It is the subset of the finite box `[2, ℓ]^r` cut out by these conditions. -/
@[collatz_pos_dens "def_rn_fp_raw"]
def firstPassageWords (s r : ℕ) (ℓ : ℤ) : Finset (Fin r → ℤ) :=
  (Fintype.piFinset fun _ => Icc 2 ℓ).filter fun c =>
    (∀ i, 2 ≤ c i) ∧ (∀ i : Fin r, (i : ℕ) + 1 = r → c i ∈ ({4, 5} : Set ℤ)) ∧
      ∑ i, c i = ℓ ∧
      ∀ i : Fin r, (i : ℕ) + 1 < r → c i ∈ ({4, 5} : Set ℤ) → ∑ j ∈ Iic i, c j ≤ s

/-- Membership in `𝒟_s(r, ℓ)`: the letters are at least `2`, the last letter lies in `{4, 5}`, the
letters sum to `ℓ`, and every earlier letter in `{4, 5}` ends a prefix of sum at most `s`. -/
theorem mem_firstPassageWords {s r : ℕ} {ℓ : ℤ} {c : Fin r → ℤ} :
    c ∈ firstPassageWords s r ℓ ↔ (∀ i, 2 ≤ c i) ∧
      (∀ i : Fin r, (i : ℕ) + 1 = r → c i ∈ ({4, 5} : Set ℤ)) ∧ ∑ i, c i = ℓ ∧
      ∀ i : Fin r, (i : ℕ) + 1 < r → c i ∈ ({4, 5} : Set ℤ) → ∑ j ∈ Iic i, c j ≤ s := by
  rw [firstPassageWords, mem_filter, and_iff_right_iff_imp]
  rintro ⟨h2, -, hs, -⟩
  refine Fintype.mem_piFinset.2 fun i => mem_Icc.2 ⟨h2 i, ?_⟩
  rw [← hs]
  exact single_le_sum (fun j _ => le_trans (by omega) (h2 j)) (mem_univ i)

/-- Every letter of a word in `𝒟_s(r, ℓ)` is at least `2`. -/
theorem firstPassageWords_two_le {s r : ℕ} {ℓ : ℤ} {c : Fin r → ℤ}
    (hc : c ∈ firstPassageWords s r ℓ) (i : Fin r) : 2 ≤ c i :=
  (mem_firstPassageWords.1 hc).1 i

/-- The letters of a word in `𝒟_s(r, ℓ)` sum to `ℓ`. -/
theorem firstPassageWords_sum_eq {s r : ℕ} {ℓ : ℤ} {c : Fin r → ℤ}
    (hc : c ∈ firstPassageWords s r ℓ) : ∑ i, c i = ℓ :=
  (mem_firstPassageWords.1 hc).2.2.1

/-- Every letter of a word in `𝒟_s(r, ℓ)` lies in `[2, ℓ]`. -/
theorem firstPassageWords_mem_Icc {s r : ℕ} {ℓ : ℤ} {c : Fin r → ℤ}
    (hc : c ∈ firstPassageWords s r ℓ) (i : Fin r) : c i ∈ Icc 2 ℓ :=
  Fintype.mem_piFinset.1 (mem_filter.1 hc).1 i

/-- The last letter of a word in `𝒟_s(r+1, ℓ)` lies in `{4, 5}`. -/
theorem firstPassageWords_last_mem {s r : ℕ} {ℓ : ℤ} {c : Fin (r + 1) → ℤ}
    (hc : c ∈ firstPassageWords s (r + 1) ℓ) : c (Fin.last r) ∈ ({4, 5} : Set ℤ) :=
  (mem_firstPassageWords.1 hc).2.1 _ (by simp)

/-- In a word of `𝒟_s(r, ℓ)`, an earlier letter in `{4, 5}` ends a prefix of sum at most `s`. -/
theorem firstPassageWords_prefix_le {s r : ℕ} {ℓ : ℤ} {c : Fin r → ℤ}
    (hc : c ∈ firstPassageWords s r ℓ) (i : Fin r) (hi : (i : ℕ) + 1 < r)
    (h45 : c i ∈ ({4, 5} : Set ℤ)) : ∑ j ∈ Iic i, c j ≤ s :=
  (mem_firstPassageWords.1 hc).2.2.2 i hi h45

end CollatzPosDens
