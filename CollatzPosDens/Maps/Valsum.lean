/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word

/-!
# The valuation sum of a word

For a word `w = (a₁, …, a_d) ∈ 𝕎`, its *valuation sum* is `A(w) = a₁ + ⋯ + a_d`, the total
power of `2` divided out along the corresponding inverse Syracuse orbit.

## Main definitions

* `CollatzPosDens.Word.valSum`: the valuation sum `A(w)` of a word, as a natural number.
* `CollatzPosDens.Word.incrHead`: the word with its first letter raised by one.

## Main results

* `CollatzPosDens.Word.valSum_append`: `A(uv) = A(u) + A(v)`.
* `CollatzPosDens.Word.length_le_valSum`: `|w| ≤ A(w)`, since every letter is positive.
* `CollatzPosDens.Word.le_valSum_of_mem`: every letter is at most `A(w)`.
* `CollatzPosDens.Word.finite_setOf_valSum_le`: there are finitely many words with `A(w) ≤ B`.

## Implementation notes

The letters of a word are positive integers (`ℕ+`), but `A(w)` is taken in `ℕ` so that the
empty word has `A(∅) = 0`; it is the sum of the letters coerced to `ℕ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

/-- The valuation sum `A(w) = a₁ + ⋯ + a_d` of a word `w = (a₁, …, a_d)`, in `ℕ`. -/
@[collatz_pos_dens "def_valsum"]
def valSum (w : Word) : ℕ := (w.map ((↑) : ℕ+ → ℕ)).sum

/-- The empty word has valuation sum `0`. -/
@[simp]
theorem valSum_nil : valSum [] = 0 := rfl

/-- `A(a w) = a + A(w)`. -/
@[simp]
theorem valSum_cons (a : ℕ+) (w : Word) : valSum (a :: w) = a + valSum w := by
  simp [valSum]

/-- A one-letter word has valuation sum equal to its letter. -/
theorem valSum_singleton (a : ℕ+) : valSum [a] = a := by
  simp [valSum]

/-- The valuation sum is additive under concatenation: `A(uv) = A(u) + A(v)`. -/
@[simp]
theorem valSum_append (u v : Word) : valSum (u ++ v) = valSum u + valSum v := by
  simp [valSum]

/-- The valuation sum of a prefix is at most that of the word. -/
theorem valSum_le_of_isPrefix {u w : Word} (h : u <+: w) : valSum u ≤ valSum w := by
  obtain ⟨v, rfl⟩ := h
  simp

/-- The length of a word is at most its valuation sum: `|w| ≤ A(w)`. -/
theorem length_le_valSum (w : Word) : w.length ≤ valSum w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.length_cons, valSum_cons]
    have := a.pos
    omega

/-- A word has valuation sum `0` exactly when it is empty. -/
@[simp]
theorem valSum_eq_zero_iff {w : Word} : valSum w = 0 ↔ w = [] := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have := length_le_valSum w
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- Every letter of a word is at most its valuation sum. -/
theorem le_valSum_of_mem {a : ℕ+} {w : Word} (ha : a ∈ w) : (a : ℕ) ≤ valSum w :=
  List.le_sum_of_mem (List.mem_map_of_mem ha)

/-- There are finitely many words of valuation sum at most `B`. -/
theorem finite_setOf_valSum_le (B : ℕ) : {w : Word | valSum w ≤ B}.Finite := by
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    have hsub : {w : Word | valSum w ≤ B} ⊆
        {[]} ∪ ⋃ a ∈ {a : ℕ+ | (a : ℕ) ≤ B},
          (fun w : Word => a :: w) '' {w : Word | valSum w ≤ B - a} := by
      rintro (_ | ⟨a, w⟩) hw
      · exact Or.inl rfl
      · simp only [Set.mem_ofPred_eq, valSum_cons] at hw
        refine Or.inr (Set.mem_biUnion (x := a) (by simp; omega) ?_)
        exact ⟨w, by simp; omega, rfl⟩
    refine (Set.finite_singleton _).union (Set.Finite.biUnion ?_ fun a ha => ?_) |>.subset hsub
    · exact (Set.finite_Iic B).preimage PNat.coe_injective.injOn
    · have ha : (a : ℕ) ≤ B := ha
      exact (ih (B - a) (by have := a.pos; omega)).image _

/-- Raise the first letter of a word by one (the empty word is left unchanged). -/
def incrHead : Word → Word
  | [] => []
  | a :: w => (a + 1) :: w

/-- Raising the first letter of the empty word leaves it empty. -/
@[simp]
theorem incrHead_nil : incrHead [] = [] := rfl

/-- Raising the first letter of `a :: w` gives `(a + 1) :: w`. -/
@[simp]
theorem incrHead_cons (a : ℕ+) (w : Word) : incrHead (a :: w) = (a + 1) :: w := rfl

/-- Raising the first letter by one is injective on words. -/
theorem incrHead_injective : Function.Injective incrHead := by
  intro x y h
  rcases x with _ | ⟨a, x⟩ <;> rcases y with _ | ⟨c, y⟩ <;> simp_all

end Word

end CollatzPosDens
