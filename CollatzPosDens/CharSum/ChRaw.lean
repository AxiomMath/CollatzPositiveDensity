/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import CollatzPosDens.Attr

/-!
# The raw letter prefix of a list of blocks

A block is a pair `β = (c, e)` of a word `c` (its nonclosing letters) and a closing letter `e`.
For blocks `β¹ = (c¹, e¹), …, βᴺ = (cᴺ, eᴺ)` consider the concatenation
`c¹ (e¹) c² (e²) ⋯ cᴺ (eᴺ)`, in which each block's nonclosing letters are followed by its
closing letter. It has length `|c¹| + ⋯ + |cᴺ| + N`. For `0 ≤ J' ≤ |c¹| + ⋯ + |cᴺ| + N`, the raw
word `raw_{J'}(β¹, …, βᴺ)` is its prefix of length `J'`.

## Main definitions

* `CollatzPosDens.chRaw J β`: the first `J` letters of the concatenation
  `c¹ (e¹) ⋯ cᴺ (eᴺ)` of the blocks `β = [(c¹, e¹), …, (cᴺ, eᴺ)]`.

## Main results

* `CollatzPosDens.chRaw_length_concat`: the concatenation has length
  `|c¹| + ⋯ + |cᴺ| + N`.
* `CollatzPosDens.length_chRaw`: if `J ≤ |c¹| + ⋯ + |cᴺ| + N` then `raw_J(β)` has length
  exactly `J`.
* `CollatzPosDens.chRaw_cons_nil_succ`, `CollatzPosDens.chRaw_cons_cons_succ`: the
  one-letter recursions `raw_{J+1}((∅, e) β) = (e) raw_J(β)` and
  `raw_{J+1}(((a) c', e) β) = (a) raw_J((c', e) β)`.

## Implementation notes

A list of blocks is a `List (List α × α)`, so `N` is its length. The letters are taken in an
arbitrary type `α` rather than `ℤ`, and no condition such as `e ∈ {4, 5}` is imposed on the
closing letters: such a condition restricts the blocks summed over, not the operation. The
prefix is taken for every `J : ℕ` (by `List.take`); the bound `J ≤ |c¹| + ⋯ + |cᴺ| + N` is
needed only for the word to have length `J`, and appears as the hypothesis of `length_chRaw`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.3.
-/

@[expose] public section

namespace CollatzPosDens

variable {α : Type*}

/-- The raw word `raw_J(β¹, …, βᴺ)`: the first `J` letters of the concatenation
`c¹ (e¹) c² (e²) ⋯ cᴺ (eᴺ)` of the blocks `βᵏ = (cᵏ, eᵏ)`, each block's nonclosing letters
followed by its closing letter. -/
@[collatz_pos_dens "def_ch_raw"]
def chRaw (J : ℕ) (β : List (List α × α)) : List α :=
  (β.flatMap fun b => b.1 ++ [b.2]).take J

/-- `raw_J(β)` is the first `J` letters of the concatenation `c¹ (e¹) ⋯ cᴺ (eᴺ)`. -/
theorem chRaw_def (J : ℕ) (β : List (List α × α)) :
    chRaw J β = (β.flatMap fun b => b.1 ++ [b.2]).take J := rfl

/-- The concatenation `c¹ (e¹) ⋯ cᴺ (eᴺ)` has length `|c¹| + ⋯ + |cᴺ| + N`. -/
theorem chRaw_length_concat (β : List (List α × α)) :
    (β.flatMap fun b => b.1 ++ [b.2]).length = (β.map fun b => b.1.length).sum + β.length := by
  induction β with
  | nil => simp
  | cons b β ih => simp [List.flatMap_cons, ih]; omega

/-- If `J ≤ |c¹| + ⋯ + |cᴺ| + N`, the raw word `raw_J(β¹, …, βᴺ)` has length `J`. -/
theorem length_chRaw {J : ℕ} {β : List (List α × α)}
    (hJ : J ≤ (β.map fun b => b.1.length).sum + β.length) :
    (chRaw J β).length = J := by
  rw [chRaw, List.length_take, chRaw_length_concat]
  omega

/-- If `J ≤ N`, the raw word `raw_J(β¹, …, βᴺ)` has length `J`. -/
theorem length_chRaw_of_le_length {J : ℕ} {β : List (List α × α)} (hJ : J ≤ β.length) :
    (chRaw J β).length = J :=
  length_chRaw (by omega)

/-- The raw word of length `0` is empty. -/
@[simp]
theorem chRaw_zero (β : List (List α × α)) : chRaw 0 β = [] := by
  simp [chRaw]

/-- The raw word of the empty list of blocks is empty. -/
@[simp]
theorem chRaw_nil (J : ℕ) : chRaw J ([] : List (List α × α)) = [] := by
  simp [chRaw]

/-- If the first block has no nonclosing letters, `raw_{J+1}((∅, e) β) = (e) raw_J(β)`. -/
@[simp]
theorem chRaw_cons_nil_succ (J : ℕ) (e : α) (β : List (List α × α)) :
    chRaw (J + 1) (([], e) :: β) = e :: chRaw J β := by
  simp [chRaw]

/-- If the first block starts with the letter `a`,
`raw_{J+1}(((a) c', e) β) = (a) raw_J((c', e) β)`. -/
@[simp]
theorem chRaw_cons_cons_succ (J : ℕ) (a e : α) (c : List α) (β : List (List α × α)) :
    chRaw (J + 1) ((a :: c, e) :: β) = a :: chRaw J ((c, e) :: β) := by
  simp [chRaw]

/-- `raw_J(β)` is a prefix of the full concatenation `c¹ (e¹) ⋯ cᴺ (eᴺ)`. -/
theorem chRaw_prefix (J : ℕ) (β : List (List α × α)) :
    chRaw J β <+: β.flatMap fun b => b.1 ++ [b.2] :=
  List.take_prefix _ _

end CollatzPosDens
