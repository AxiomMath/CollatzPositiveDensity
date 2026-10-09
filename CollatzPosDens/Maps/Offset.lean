/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.Maps.Weight

/-!
# The offset of a word

For a word `w = (a₁, …, a_d)` the *offset* is the nonnegative rational
`off(w) = ∑_{j=1}^{d} 3^{j-1} 2^{-(a₁ + ⋯ + a_j)}`, so that `off(∅) = 0`. Together with the
multiplier `3^d 2^{-(a₁ + ⋯ + a_d)}` it describes the affine map attached to `w`.

## Main definitions

* `CollatzPosDens.off`: the offset `off(w)` of a word.

## Main results

* `CollatzPosDens.off_eq_sum`: the closed form `off(w) = ∑ 3^{j-1} 2^{-(a₁ + ⋯ + a_j)}`.
* `CollatzPosDens.off_append`: `off(uv) = off(u) + ω(u) off(v)`, with `ω(u) = 3^{|u|} 2^{-A(u)}`
  the weight of `u`.
* `CollatzPosDens.off_nonneg`: `0 ≤ off(w)`.
* `CollatzPosDens.off_take_le`: `off(w_{≤ i}) ≤ off(w)`.

## Implementation notes

`off` is defined by the recursion `off(∅) = 0`, `off(a w) = 2^{-a} (1 + 3 off(w))`, which is
the Horner form of the defining sum; `off_eq_sum` recovers the sum.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset `off(w) = ∑_{j=1}^{d} 3^{j-1} 2^{-(a₁ + ⋯ + a_j)}` of a word
`w = (a₁, …, a_d)`, defined by the Horner recursion `off(∅) = 0`,
`off(a w) = 2^{-a} (1 + 3 off(w))`; see `off_eq_sum` for the closed form. -/
@[collatz_pos_dens "def_offset"]
def off : Word → ℚ
  | [] => 0
  | a :: w => ((2 : ℚ) ^ (a : ℕ))⁻¹ * (1 + 3 * off w)

/-- The offset of the empty word is `0`. -/
@[simp]
theorem off_nil : off [] = 0 := rfl

/-- The Horner recursion `off(a w) = 2^{-a} (1 + 3 off(w))`. -/
@[simp]
theorem off_cons (a : ℕ+) (w : Word) :
    off (a :: w) = ((2 : ℚ) ^ (a : ℕ))⁻¹ * (1 + 3 * off w) := rfl

/-- Closed form of the offset: `off(w) = ∑_{j=1}^{d} 3^{j-1} 2^{-(a₁ + ⋯ + a_j)}`, written
with `j` running over `0, …, d - 1` and `a₁ + ⋯ + a_{j+1}` the valuation sum of the prefix
`w.take (j + 1)`. -/
@[collatz_pos_dens "def_offset"]
theorem off_eq_sum (w : Word) :
    off w = ∑ j ∈ Finset.range w.length,
      (3 : ℚ) ^ j * ((2 : ℚ) ^ Word.valSum (w.take (j + 1)))⁻¹ := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [off_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.take_succ_cons, Word.valSum_cons, pow_add, mul_inv, pow_succ,
      List.take_zero, Word.valSum_nil, pow_zero, mul_one, one_mul, add_zero,
      Finset.mul_sum, mul_add]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The offset is nonnegative. -/
theorem off_nonneg (w : Word) : 0 ≤ off w := by
  induction w with
  | nil => simp
  | cons a w ih => rw [off_cons]; positivity

/-- The offset is a cocycle for the weight: `off(uv) = off(u) + ω(u) off(v)`, where
`ω(u) = 3^{|u|} 2^{-A(u)}`. -/
@[collatz_pos_dens "lem_s05_offset_concat"]
theorem off_append (u v : Word) : off (u ++ v) = off u + u.weight * off v := by
  induction u with
  | nil => simp [Word.weight_nil]
  | cons a u ih =>
    rw [List.cons_append, off_cons, off_cons, ih, Word.weight_cons]
    ring

/-- The offset of a prefix is at most the offset of the word: `off(w_{≤ i}) ≤ off(w)`. -/
theorem off_take_le (w : Word) (i : ℕ) : off (w.take i) ≤ off w := by
  conv_rhs => rw [← List.take_append_drop i w]
  rw [off_append]
  exact le_add_of_nonneg_right (mul_nonneg (Word.weight_pos _).le (off_nonneg _))

end CollatzPosDens
