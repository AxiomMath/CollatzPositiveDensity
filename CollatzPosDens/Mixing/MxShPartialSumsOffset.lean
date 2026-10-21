/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Mixing.MxShPartialSums
public import CollatzPosDens.Mixing.MxShSubsetOffset

/-!
# The offset of a word is the offset of its set of partial sums

For a word `v = (a₁, …, a_d)` with partial sums `S_i = a₁ + ⋯ + a_i`, the partial sums are
strictly increasing because every letter is positive, so `S_i` has exactly `i - 1` partial sums
below it. Hence the set offset of `Pt(v) = {S₁, …, S_d}` is
$$\operatorname{Of}(\mathrm{Pt}(v)) = \sum_{i=1}^d 3^{i-1} 2^{-S_i} = \mathrm{off}(v).$$

## Main results

* `CollatzPosDens.setOffset_map_addLeftEmbedding`: translating a set by `c` multiplies its
  offset by `2^{-c}`.
* `CollatzPosDens.Word.off_eq_setOffset_partialSums`: `off(v) = Of(Pt(v))`.

## Implementation notes

The identity is proved by induction on the word rather than through the closed sum: the partial
sums satisfy `Pt(a v) = {a} ∪ (a + Pt(v))`, with `a` below every element of `a + Pt(v)`, so the
Horner step of the set offset matches the Horner recursion `off(a v) = 2^{-a}(1 + 3 off(v))`.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Translating a finite set of positions by `c` multiplies its offset by `2^{-c}`:
`Of(c + S) = 2^{-c} Of(S)`. -/
theorem setOffset_map_addLeftEmbedding (c : ℕ) (S : Finset ℕ) :
    setOffset (S.map (addLeftEmbedding c)) = ((2 : ℚ) ^ c)⁻¹ * setOffset S := by
  unfold setOffset
  rw [sum_map, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  have : (S.map (addLeftEmbedding c)).filter (· < addLeftEmbedding c s) =
      (S.filter (· < s)).map (addLeftEmbedding c) := by
    rw [filter_map]
    congr 1
    exact filter_congr fun t _ => by simp
  rw [this, card_map, addLeftEmbedding_apply, pow_add, mul_inv]
  ring

namespace Word

/-- The offset of a word equals the set offset of its partial sums: `off(v) = Of(Pt(v))`. -/
@[collatz_pos_dens "lem_mx_sh_partial_sums_offset"]
theorem off_eq_setOffset_partialSums (v : Word) : off v = setOffset (partialSums v) := by
  induction v with
  | nil => simp
  | cons a v ih =>
    rw [partialSums_cons, setOffset_insert_of_forall_lt, setOffset_map_addLeftEmbedding, ← ih,
      off_cons]
    · ring
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_map.1 hs
      have := pos_of_mem_partialSums ht
      simp only [addLeftEmbedding_apply]
      omega

end Word

end CollatzPosDens
