/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPoint

/-!
# Partial sums of block points

For a list of blocks `β = (β¹, …, β^K)` and `0 ≤ i ≤ K`, the `i`-th block path point is
`Bp_i(β) = bpt(β¹) + ⋯ + bpt(β^i)`, the lattice point reached after the first `i` blocks when
the paired letters are read as a renewal sequence. In particular `Bp_0(β) = (0, 0)`, and
`Bp_{i+1}(β) = Bp_i(β) + bpt(β^{i+1})`.

## Main definitions

* `CollatzPosDens.chBlockPath`: the partial sum `Bp_i(β)` of block points.

## Main results

* `CollatzPosDens.chBlockPath_zero`: `Bp_0(β) = (0, 0)`.
* `CollatzPosDens.chBlockPath_succ`: `Bp_{i+1}(β) = Bp_i(β) + bpt(β^{i+1})` for `i < K`.
* `CollatzPosDens.chBlockPath_fst`: the first coordinate of `Bp_i(β)` is `min(i, K)` plus
  the total number of nonclosing letters of the first `i` blocks; in particular it is nonnegative
  (`chBlockPath_fst_nonneg`), so `Bp_i(β) ∈ ℕ × ℤ`.

## Implementation notes

A list `β ∈ 𝔅^K` is modelled as `β : List (List ℤ × ℤ)`, with `K = β.length`, following
`chBlockPoint`, which is defined on all of `List ℤ × ℤ`. Since `bpt` takes values in `ℤ × ℤ`,
so does `chBlockPath`; that the first coordinate is a natural number is the separate statement
`chBlockPath_fst_nonneg`. The index `i` is any natural number: for `i ≥ K` the definition
returns the full sum `Bp_K(β)`, which is a harmless extension of the range `0 ≤ i ≤ K`.

## References

* [Mazur, *Collatz positive density*], §7.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The partial sum `Bp_i(β) = bpt(β¹) + ⋯ + bpt(β^i)` of the block points of the first `i`
blocks of `β`. -/
@[collatz_pos_dens "def_ch_block_path"]
def chBlockPath (β : List (List ℤ × ℤ)) (i : ℕ) : ℤ × ℤ :=
  ((β.take i).map chBlockPoint).sum

/-- `Bp_0(β) = (0, 0)`. -/
@[simp]
lemma chBlockPath_zero (β : List (List ℤ × ℤ)) : chBlockPath β 0 = 0 := by
  simp [chBlockPath]

/-- The empty list of blocks has all partial sums zero. -/
@[simp]
lemma chBlockPath_nil (i : ℕ) : chBlockPath [] i = 0 := by
  simp [chBlockPath]

/-- Partial sums of `b :: β`: `Bp_{i+1}(b :: β) = bpt(b) + Bp_i(β)`. -/
@[simp]
lemma chBlockPath_cons_succ (b : List ℤ × ℤ) (β : List (List ℤ × ℤ)) (i : ℕ) :
    chBlockPath (b :: β) (i + 1) = chBlockPoint b + chBlockPath β i := by
  simp [chBlockPath]

/-- `Bp_{i+1}(β) = Bp_i(β) + bpt(β^{i+1})` for `i < K`. -/
lemma chBlockPath_succ (β : List (List ℤ × ℤ)) {i : ℕ} (hi : i < β.length) :
    chBlockPath β (i + 1) = chBlockPath β i + chBlockPoint β[i] := by
  simp only [chBlockPath, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]

/-- Beyond the length of `β`, the partial sums are constant, equal to `Bp_K(β)`. -/
lemma chBlockPath_of_length_le (β : List (List ℤ × ℤ)) {i : ℕ} (hi : β.length ≤ i) :
    chBlockPath β i = (β.map chBlockPoint).sum := by
  simp [chBlockPath, List.take_of_length_le hi]

/-- Partial sums along a concatenation: for `i ≤ |β|`, `Bp_i(β ++ γ) = Bp_i(β)`. -/
lemma chBlockPath_append_of_le (β γ : List (List ℤ × ℤ)) {i : ℕ} (hi : i ≤ β.length) :
    chBlockPath (β ++ γ) i = chBlockPath β i := by
  simp [chBlockPath, List.take_append_of_le_length hi]

/-- The first coordinate of `Bp_i(β)` is `min(i, K)` plus the number of nonclosing letters in the
first `i` blocks. -/
lemma chBlockPath_fst (β : List (List ℤ × ℤ)) (i : ℕ) :
    (chBlockPath β i).1 =
      (min i β.length : ℕ) + (((β.take i).map fun b => (b.1.length : ℤ))).sum := by
  induction β generalizing i with
  | nil => simp
  | cons b β ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [chBlockPath_cons_succ, Prod.fst_add, ih, chBlockPoint_fst]
      simp only [List.length_cons, Nat.add_min_add_right, List.take_succ_cons, List.map_cons,
        List.sum_cons]
      push_cast
      ring

/-- The first coordinate of `Bp_i(β)` is nonnegative, so `Bp_i(β) ∈ ℕ × ℤ`. -/
lemma chBlockPath_fst_nonneg (β : List (List ℤ × ℤ)) (i : ℕ) : 0 ≤ (chBlockPath β i).1 := by
  rw [chBlockPath_fst]
  refine add_nonneg (by positivity) (List.sum_nonneg ?_)
  simp only [List.mem_map]
  rintro _ ⟨b, -, rfl⟩
  positivity

/-- The second coordinate of `Bp_i(β)` is the sum of all letters of the first `i` blocks. -/
lemma chBlockPath_snd (β : List (List ℤ × ℤ)) (i : ℕ) :
    (chBlockPath β i).2 = ((β.take i).map fun b => b.1.sum + b.2).sum := by
  induction β generalizing i with
  | nil => simp
  | cons b β ih =>
    cases i with
    | zero => simp
    | succ i => simp [ih]

end CollatzPosDens
