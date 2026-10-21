/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import CollatzPosDens.Attr

/-!
# The offset of a set of positions

For a finite set `S` of positions the *offset* of `S` is the nonnegative rational
$$\operatorname{Of}(S) = \sum_{s \in S} 3^{\#\{t \in S : t < s\}}\, 2^{-s}.$$
Listing `S = {s₁ < ⋯ < s_d}`, this is `∑ᵢ 3^{i-1} 2^{-sᵢ}`, the offset of the word whose
partial sums are `s₁, …, s_d`. Adding an element below all others gives the Horner step
`Of({a} ∪ S) = 2^{-a} + 3 Of(S)`, and adding elements anywhere can only increase the offset.

## Main definitions

* `CollatzPosDens.setOffset`: the offset `Of(S)` of a finite set `S ⊆ ℕ`.

## Main results

* `CollatzPosDens.setOffset_nonneg`, `CollatzPosDens.setOffset_pos`: `0 ≤ Of(S)`, with
  `0 < Of(S)` when `S` is nonempty.
* `CollatzPosDens.setOffset_insert_of_forall_lt`: `Of({a} ∪ S) = 2^{-a} + 3 Of(S)` when `a` lies
  below every element of `S`.
* `CollatzPosDens.setOffset_mono`: `S ⊆ T` implies `Of(S) ≤ Of(T)`.

## Implementation notes

The offset is usually considered for sets of positive integers; the definition is stated for
every finite `S ⊆ ℕ`, where the formula makes sense verbatim. The value lies in `ℚ`, like the
word offset `CollatzPosDens.off`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset `Of(S) = ∑_{s ∈ S} 3^{#{t ∈ S : t < s}} 2^{-s}` of a finite set `S` of positions. -/
@[collatz_pos_dens "def_mx_sh_subset_offset"]
def setOffset (S : Finset ℕ) : ℚ :=
  ∑ s ∈ S, (3 : ℚ) ^ (S.filter (· < s)).card * ((2 : ℚ) ^ s)⁻¹

/-- The empty set has offset `0`. -/
@[simp]
theorem setOffset_empty : setOffset ∅ = 0 := by
  simp [setOffset]

/-- A single position `a` has offset `2^{-a}`. -/
@[simp]
theorem setOffset_singleton (a : ℕ) : setOffset {a} = ((2 : ℚ) ^ a)⁻¹ := by
  simp [setOffset, Finset.filter_singleton]

/-- The offset is nonnegative. -/
theorem setOffset_nonneg (S : Finset ℕ) : 0 ≤ setOffset S := by
  unfold setOffset
  positivity

/-- A nonempty set has positive offset. -/
theorem setOffset_pos {S : Finset ℕ} (hS : S.Nonempty) : 0 < setOffset S := by
  unfold setOffset
  exact Finset.sum_pos (fun _ _ => by positivity) hS

/-- Adding a position `a` below every element of `S`: `Of({a} ∪ S) = 2^{-a} + 3 Of(S)`. -/
theorem setOffset_insert_of_forall_lt {a : ℕ} {S : Finset ℕ} (h : ∀ s ∈ S, a < s) :
    setOffset (insert a S) = ((2 : ℚ) ^ a)⁻¹ + 3 * setOffset S := by
  have ha : a ∉ S := fun hm => lt_irrefl a (h a hm)
  unfold setOffset
  rw [Finset.sum_insert ha, Finset.mul_sum]
  congr 1
  · have : (insert a S).filter (· < a) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false, not_and,
        not_lt]
      rintro (rfl | ht)
      · exact le_rfl
      · exact (h t ht).le
    simp [this]
  · refine Finset.sum_congr rfl fun s hs => ?_
    have : (insert a S).filter (· < s) = insert a (S.filter (· < s)) :=
      by simp [Finset.filter_insert, h s hs]
    rw [this, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.1 hm).1), pow_succ]
    ring

/-- The offset is monotone: `S ⊆ T` implies `Of(S) ≤ Of(T)`. -/
theorem setOffset_mono {S T : Finset ℕ} (hST : S ⊆ T) : setOffset S ≤ setOffset T := by
  unfold setOffset
  calc ∑ s ∈ S, (3 : ℚ) ^ (S.filter (· < s)).card * ((2 : ℚ) ^ s)⁻¹
      ≤ ∑ s ∈ S, (3 : ℚ) ^ (T.filter (· < s)).card * ((2 : ℚ) ^ s)⁻¹ := by
        refine Finset.sum_le_sum fun s _ => ?_
        gcongr
        norm_num
    _ ≤ ∑ s ∈ T, (3 : ℚ) ^ (T.filter (· < s)).card * ((2 : ℚ) ^ s)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hST fun _ _ _ => by positivity

end CollatzPosDens
