/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.OrdinaryTime.S07SelectedPair
public import CollatzPosDens.Seed.S05ConcatWord

/-!
# The full word of a selected pair

For a selected pair `(h, w)` whose history is the tuple `h = (w₀, …, w_{n-1})`, its *full word*
is the concatenation `𝐰(h, w) = ŵ(h) w = w₀ ⋯ w_{n-1} w ∈ 𝕎` of the concatenated word `ŵ(h)`
(`CollatzPosDens.concatWord`) of `h` and the terminal word `w`; it is `w` itself if `n = 0`.

## Main definitions

* `CollatzPosDens.fullWord h w`: the concatenation `ŵ(h) w`.

## Main results

* `CollatzPosDens.length_fullWord`: `|𝐰(h, w)| = ∑ i, |wᵢ| + |w|`.
* `CollatzPosDens.fullWord_succ`: `𝐰((w₀, …, w_n), w) = w₀ 𝐰((w₁, …, w_n), w)`.

## Implementation notes

A history `(w₀, …, w_{n-1})` of generation `n` is a tuple `Fin n → Word`. The concatenation
`ŵ(h) w` makes sense for a tuple `h : Fin m → Word` of any length `m` and any word `w`, so the
definition is stated for all such pairs and does not require `(h, w)` to be a selected pair; a
selected pair of generation `n` is the case `m = n`.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- The *full word* `𝐰(h, w) = ŵ(h) w` of a pair `(h, w)`: the concatenated word of the tuple
`h` followed by the word `w`. For a selected pair of generation `n`, `h = (w₀, …, w_{n-1})` is
a tuple `Fin n → Word` and `𝐰(h, w) = w₀ ⋯ w_{n-1} w`. -/
@[collatz_pos_dens "def_s07_full_word"]
def fullWord (h : Fin n → Word) (w : Word) : Word :=
  concatWord h ++ w

/-- The full word of a pair with the empty history is its word. -/
@[simp]
theorem fullWord_zero (h : Fin 0 → Word) (w : Word) : fullWord h w = w := by
  simp [fullWord]

/-- Peeling off the first block of the history:
`𝐰((w₀, …, w_n), w) = w₀ 𝐰((w₁, …, w_n), w)`. -/
theorem fullWord_succ (h : Fin (n + 1) → Word) (w : Word) :
    fullWord h w = h 0 ++ fullWord (Fin.tail h) w := by
  rw [fullWord, fullWord, concatWord_succ', List.append_assoc]
  rfl

/-- The full word of a history with first block `a` is `a` followed by the full word of
the rest. -/
@[simp]
theorem fullWord_cons (a : Word) (h : Fin n → Word) (w : Word) :
    fullWord (Fin.cons a h) w = a ++ fullWord h w := by
  simp [fullWord_succ]

/-- The length of the full word is the total length of the history plus that of the word. -/
@[simp]
theorem length_fullWord (h : Fin n → Word) (w : Word) :
    (fullWord h w).length = ∑ i, (h i).length + w.length := by
  rw [fullWord, List.length_append, length_concatWord]

/-- The word `w` is a suffix of the full word `𝐰(h, w)`. -/
theorem suffix_fullWord (h : Fin n → Word) (w : Word) : w <:+ fullWord h w :=
  List.suffix_append _ _

end CollatzPosDens
