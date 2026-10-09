/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The concatenated word of a tuple of words

For `n ∈ ℕ` and a tuple `t = (w₀, …, w_{n-1})` of words, the *concatenated word* of `t` is
`ŵ(t) = w₀ w₁ ⋯ w_{n-1}`. Its length is the sum of the lengths of the `wⱼ`, and it is built
up one block at a time: `ŵ(w₀, …, w_n) = ŵ(w₀, …, w_{n-1}) w_n = w₀ ŵ(w₁, …, w_n)`.

## Main definitions

* `CollatzPosDens.concatWord t`: the concatenated word `ŵ(t)` of `t : Fin n → Word`.

## Main results

* `CollatzPosDens.concatWord_succ`: `ŵ(t) = ŵ(t|_{<n}) t_n`.
* `CollatzPosDens.concatWord_succ'`: `ŵ(t) = t₀ ŵ(t ∘ succ)`.
* `CollatzPosDens.concatWord_cons`: `ŵ(w, t) = w ŵ(t)`.
* `CollatzPosDens.concatWord_snoc`: `ŵ(t, w) = ŵ(t) w`.
* `CollatzPosDens.flatten_take_succ_ofFn`: flattening the first `j + 1` blocks appends `w_j`.
* `CollatzPosDens.length_concatWord`: `|ŵ(t)| = ∑ⱼ |wⱼ|`.
* `CollatzPosDens.infix_concatWord`: each block `wⱼ` is a factor of `ŵ(t)`.
* `CollatzPosDens.concatWord_castSucc_prefix`: `ŵ(t|_{<n})` is a prefix of `ŵ(t)`.

## Implementation notes

A tuple `(w₀, …, w_{n-1})` is a function `Fin n → Word`, and `ŵ(t)` is the flattening of the
list `[w₀, …, w_{n-1}]`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- The concatenated word `ŵ(t) = w₀ w₁ ⋯ w_{n-1}` of a tuple `t = (w₀, …, w_{n-1})` of
words. -/
@[collatz_pos_dens "def_s05_concat_word"]
def concatWord (t : Fin n → Word) : Word := (List.ofFn t).flatten

/-- `ŵ(t)` is the flattening of the list `[w₀, …, w_{n-1}]`. -/
theorem concatWord_def (t : Fin n → Word) : concatWord t = (List.ofFn t).flatten := rfl

/-- The concatenated word of the empty tuple is the empty word. -/
@[simp] theorem concatWord_zero (t : Fin 0 → Word) : concatWord t = [] := rfl

/-- Appending the last block: `ŵ(w₀, …, w_n) = ŵ(w₀, …, w_{n-1}) w_n`. -/
theorem concatWord_succ (t : Fin (n + 1) → Word) :
    concatWord t = concatWord (fun i : Fin n => t i.castSucc) ++ t (Fin.last n) := by
  rw [concatWord, concatWord, List.ofFn_succ', List.concat_eq_append, List.flatten_append,
    List.flatten_singleton]

/-- Prepending the first block: `ŵ(w₀, …, w_n) = w₀ ŵ(w₁, …, w_n)`. -/
theorem concatWord_succ' (t : Fin (n + 1) → Word) :
    concatWord t = t 0 ++ concatWord (fun i : Fin n => t i.succ) := by
  simp [concatWord, List.ofFn_succ]

/-- Flattening one more block of a tuple of words appends that block. -/
theorem flatten_take_succ_ofFn (t : Fin n → Word) {j : ℕ} (hj : j < n) :
    ((List.ofFn t).take (j + 1)).flatten = ((List.ofFn t).take j).flatten ++ t ⟨j, hj⟩ := by
  rw [List.take_add_one, List.getElem?_ofFn, List.flatten_append]
  simp [hj]

/-- Prepending a block: `ŵ(w, w₀, …, w_{n-1}) = w ŵ(w₀, …, w_{n-1})`. -/
@[simp] theorem concatWord_cons (w : Word) (t : Fin n → Word) :
    concatWord (Fin.cons w t : Fin (n + 1) → Word) = w ++ concatWord t := by
  simp [concatWord_succ']

/-- Appending a block: `ŵ(w₀, …, w_{n-1}, w) = ŵ(w₀, …, w_{n-1}) w`. -/
@[simp] theorem concatWord_snoc (t : Fin n → Word) (w : Word) :
    concatWord (Fin.snoc t w : Fin (n + 1) → Word) = concatWord t ++ w := by
  simp [concatWord_succ]

/-- The concatenated word of a one-block tuple `(w₀)` is `w₀`. -/
@[simp] theorem concatWord_one (t : Fin 1 → Word) : concatWord t = t 0 := by
  simp [concatWord_succ']

/-- The length of `ŵ(t)` is the total length `∑ⱼ |wⱼ|`. -/
theorem length_concatWord (t : Fin n → Word) :
    (concatWord t).length = ∑ j, (t j).length := by
  induction n with
  | zero => simp
  | succ n ih => rw [concatWord_succ', List.length_append, ih, Fin.sum_univ_succ]

/-- Each block `wⱼ` lies inside `ŵ(t)`. -/
theorem infix_concatWord (t : Fin n → Word) (j : Fin n) : t j <:+: concatWord t :=
  List.infix_of_mem_flatten ((List.mem_ofFn' t _).2 ⟨j, rfl⟩)

/-- The concatenation of the first `n` blocks is a prefix of the concatenation of all
`n + 1`. -/
theorem concatWord_castSucc_prefix (t : Fin (n + 1) → Word) :
    concatWord (fun i : Fin n => t i.castSucc) <+: concatWord t := by
  rw [concatWord_succ t]
  exact List.prefix_append _ _

end CollatzPosDens
