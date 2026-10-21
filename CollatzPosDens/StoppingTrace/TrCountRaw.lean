/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# The weighted white count as a sum over raw letters

Fix a level `n` and a residue `ξ ∈ G_n`, and write `R_a(p)` for the paid reward of
`(n, ξ, ε_*)`. For a base point `o ∈ 𝒫` and a block list `β ∈ 𝔅^K`, let `M = j(Bp_K(β))` and
`z = raw_M(β)`, the full concatenation of the letters of the blocks of `β`. Then the weighted
white count of all `K` blocks is the sum of the paid rewards of the raw letters, each read at
the point reached after it:
```
N^*(o, β; K) = ∑_{i=1}^{M} R_{z_i}(o + (i, σ_i(β))).
```
Indeed, the reward of the `k`-th block collects exactly the summands of the letters of that block,
and the blocks partition the positions `1, …, M`.

## Main results

* `CollatzPosDens.trCount_eq_sum_flatMap`: the identity, written over the concatenation of the
  letters of `β`, for every base point.
* `CollatzPosDens.trCount_eq_sum_chRaw`: `N^*(o, β; K) = ∑_{i=1}^{M} R_{z_i}(o + (i, σ_i(β)))`.

## Implementation notes

A list `β ∈ 𝔅^K` is a `List (List ℤ × ℤ)` with `K = β.length`, and the base point is any
`o ∈ ℤ × ℤ`. The letter `z_i` is `z.getD (i - 1) 0`; the default value is never used since
`1 ≤ i ≤ M = |z|`. The first coordinate `M = j(Bp_K(β))` is converted to a natural number by
`Int.toNat`, as in `CollatzPosDens.trRawSum`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n}

/-- The weighted white count of all blocks of `β` is the sum, over the positions `i < |w|` of the
concatenation `w = c¹ (e¹) ⋯ cᴷ (eᴷ)`, of the paid reward of the letter `w_{i+1}` at the point
`o + (i + 1, w₁ + ⋯ + w_{i+1})`. -/
theorem trCount_eq_sum_flatMap (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) :
    trCount n ξ o β β.length =
      ∑ i ∈ Finset.range (β.flatMap fun b => b.1 ++ [b.2]).length,
        chPaidReward n ξ (epsStar : ℝ) ((β.flatMap fun b => b.1 ++ [b.2]).getD i 0)
          (o + ((i : ℤ) + 1, ((β.flatMap fun b => b.1 ++ [b.2]).take (i + 1)).sum)) := by
  induction β generalizing o with
  | nil => simp
  | cons b β ih =>
    rw [List.length_cons, trCount_cons_succ, ih, List.flatMap_cons, List.length_append,
      Finset.sum_range_add, trReward]
    congr 1
    · refine Finset.sum_congr (by simp) fun i hi => ?_
      have hi : i < (b.1 ++ [b.2]).length := Finset.mem_range.1 hi
      rw [List.getD_append _ _ _ _ hi,
        List.take_append_of_le_length (l₁ := b.1 ++ [b.2]) (by omega)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hu : (b.1 ++ [b.2]).length = b.1.length + 1 := by simp
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
        show (b.1 ++ [b.2]).length + i + 1 = (b.1 ++ [b.2]).length + (i + 1) by omega,
        List.take_length_add_append, List.sum_append]
      congr 1
      ext
      · simp only [Prod.fst_add, chBlockPoint_fst, hu]
        push_cast
        ring
      · simp only [Prod.snd_add, chBlockPoint_snd, List.sum_append, List.sum_cons, List.sum_nil]
        ring

/-- **The weighted white count along the raw word.** For a base point `o`, a block list `β ∈ 𝔅^K`,
`M = j(Bp_K(β))` and `z = raw_M(β)`,
`N^*(o, β; K) = ∑_{i=1}^{M} R_{z_i}(o + (i, σ_i(β)))`. -/
@[collatz_pos_dens "lem_tr_count_raw"]
theorem trCount_eq_sum_chRaw (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) :
    trCount n ξ o β β.length =
      ∑ i ∈ Finset.Icc 1 (chBlockPath β β.length).1.toNat,
        chPaidReward n ξ (epsStar : ℝ)
          ((chRaw (chBlockPath β β.length).1.toNat β).getD (i - 1) 0)
          (o + ((i : ℤ), trRawSum β i)) := by
  rw [trCount_eq_sum_flatMap, chRaw_toNat_chBlockPath_fst, toNat_chBlockPath_fst,
    Finset.range_eq_Ico, ← Finset.sum_Ico_add_right_sub_eq (c := 1)]
  refine Finset.sum_congr (by ext; simp) fun i hi => ?_
  have hi : 1 ≤ i := by simp at hi; omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
  simp [trRawSum_eq_sum_take]

end CollatzPosDens
