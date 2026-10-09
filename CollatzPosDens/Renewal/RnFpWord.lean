/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.TakeDrop
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.Attr

/-!
# First-passage words

Let `s` be a level. A tuple `h = (h₁, …, h_K) ∈ 𝒫^K` with `K ≥ 1` is a *first-passage word* for
level `s` if the partial sums of the second coordinates stay at most `s` strictly before the end,
`l(h₁) + ⋯ + l(h_k) ≤ s` for every `0 ≤ k < K`, and the full sum exceeds it,
`l(h₁) + ⋯ + l(h_K) > s`.

## Main definitions

* `CollatzPosDens.IsFirstPassageWord`: the predicate that a list of points is a first-passage
  word for a level `s`.

## Main results

* `CollatzPosDens.isFirstPassageWord_singleton_iff`: a one-letter word `[p]` is a first-passage
  word for `s` iff `p ∈ 𝒫` and `0 ≤ s < l(p)`.
* `CollatzPosDens.isFirstPassageWord_cons_cons_iff`: `p :: q :: t` is a first-passage word for
  `s` iff `p ∈ 𝒫`, `0 ≤ s`, and `q :: t` is a first-passage word for `s - l(p)`.

## Implementation notes

Tuples are lists. The level `s` is taken in `ℤ` rather than in `ℕ`. A first-passage word for a
negative level does not exist, since the empty partial sum `0` must be at most `s`; allowing
negative levels makes the tail of a first-passage word for `s` a first-passage word for the level
`s - l(h₁)`, which is negative when `l(h₁) > s`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- A list `h = [h₁, …, h_K]` of points is a *first-passage word* for level `s` if `K ≥ 1`, every
`hᵢ ∈ 𝒫`, `l(h₁) + ⋯ + l(h_k) ≤ s` for every `0 ≤ k < K`, and `l(h₁) + ⋯ + l(h_K) > s`. -/
@[collatz_pos_dens "def_rn_fp_word"]
def IsFirstPassageWord (s : ℤ) (h : List (ℤ × ℤ)) : Prop :=
  h ≠ [] ∧ (∀ p ∈ h, p ∈ bkPoints) ∧ (∀ k < h.length, ((h.take k).map bkL).sum ≤ s) ∧
    s < (h.map bkL).sum

/-- Being a first-passage word is decidable. -/
instance (s : ℤ) (h : List (ℤ × ℤ)) : Decidable (IsFirstPassageWord s h) := by
  unfold IsFirstPassageWord bkPoints
  infer_instance

namespace IsFirstPassageWord

variable {s : ℤ} {h : List (ℤ × ℤ)}

/-- A first-passage word is nonempty. -/
theorem ne_nil (hh : IsFirstPassageWord s h) : h ≠ [] := hh.1

/-- A first-passage word has positive length. -/
theorem length_pos (hh : IsFirstPassageWord s h) : 0 < h.length :=
  List.length_pos_iff.2 hh.1

/-- Every letter of a first-passage word lies in `𝒫`. -/
theorem mem_bkPoints (hh : IsFirstPassageWord s h) {p : ℤ × ℤ} (hp : p ∈ h) : p ∈ bkPoints :=
  hh.2.1 p hp

/-- If `h` is a first-passage word for `s` and `k < K`, then `l(h₁) + ⋯ + l(h_k) ≤ s`. -/
theorem sum_take_le (hh : IsFirstPassageWord s h) {k : ℕ} (hk : k < h.length) :
    ((h.take k).map bkL).sum ≤ s :=
  hh.2.2.1 k hk

/-- If `h` is a first-passage word for `s`, then `s < l(h₁) + ⋯ + l(h_K)`. -/
theorem lt_sum (hh : IsFirstPassageWord s h) : s < (h.map bkL).sum := hh.2.2.2

/-- The level of a first-passage word is nonnegative. -/
theorem nonneg (hh : IsFirstPassageWord s h) : 0 ≤ s := by
  simpa using hh.sum_take_le hh.length_pos

end IsFirstPassageWord

/-- The empty word is not a first-passage word for any level. -/
theorem not_isFirstPassageWord_nil (s : ℤ) : ¬ IsFirstPassageWord s [] := fun h => h.1 rfl

/-- A one-letter word is a first-passage word for `s` iff its letter lies in `𝒫` and
`0 ≤ s < l(p)`. -/
theorem isFirstPassageWord_singleton_iff {s : ℤ} {p : ℤ × ℤ} :
    IsFirstPassageWord s [p] ↔ p ∈ bkPoints ∧ 0 ≤ s ∧ s < bkL p := by
  simp [IsFirstPassageWord]

/-- A word with at least two letters is a first-passage word for `s` iff its first letter lies
in `𝒫`, `0 ≤ s`, and the rest is a first-passage word for `s - l(p)`. -/
theorem isFirstPassageWord_cons_cons_iff {s : ℤ} {p q : ℤ × ℤ} {t : List (ℤ × ℤ)} :
    IsFirstPassageWord s (p :: q :: t) ↔
      p ∈ bkPoints ∧ 0 ≤ s ∧ IsFirstPassageWord (s - bkL p) (q :: t) := by
  constructor
  · intro hh
    refine ⟨hh.mem_bkPoints (by simp), hh.nonneg, by simp, fun r hr => hh.mem_bkPoints
      (List.mem_cons_of_mem _ hr), fun k hk => ?_, ?_⟩
    · grind [hh.sum_take_le (k := k + 1) (by simpa using hk)]
    · grind [hh.lt_sum]
  · rintro ⟨hp, hs, hh⟩
    refine ⟨by simp, List.forall_mem_cons.2 ⟨hp, fun _ => hh.mem_bkPoints⟩, fun k hk => ?_, ?_⟩
    · rcases k with _ | k
      · simpa using hs
      · grind [hh.sum_take_le (k := k) (by simpa using hk)]
    · grind [hh.lt_sum]

end CollatzPosDens
