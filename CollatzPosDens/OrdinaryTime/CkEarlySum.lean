/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesB42
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Logic.Function.Iterate

/-!
# The early sum of the scales

The scales `b_j` satisfy
$$180000 \sum_{j=0}^{2253} b_j \le 11 \cdot 2^{41} \cdot 10^{10}.$$

Since the scales are nondecreasing and `b_{42} = 256`, the first `42` scales sum to at most
`42 · 256 = 10752`. From `b_{42} = 256` on, every scale is at least `256`, so the increment
takes its fallback value and `b_{j+1} = b_j + ⌈b_j/100⌉`. Running this integer recursion from
`256` and summing gives `∑_{j=42}^{2253} b_j = 110065888051444`, whence the whole sum is at most
`110065888062196`, and `180000 · 110065888062196 ≤ 11 · 2^{41} · 10^{10}`.

## Main results

* `CollatzPosDens.scale_early_sum_le`: `180000 ∑_{j<2254} b_j ≤ 11 · 2^{41} · 10^{10}`.

## Implementation notes

The tail sum is evaluated in the kernel through an accumulator-passing mirror of the
recursion `b ↦ b + ⌈b/100⌉` (with `⌈b/100⌉ = (b + 99)/100`), which runs in linear time on
natural-number literals; a lemma identifies the mirror with the sum of iterates.
-/

@[expose] public section

namespace CollatzPosDens

/-- Accumulator-passing evaluation of `s + ∑_{k<n} f^[k] b` for `f b = b + ⌈b/100⌉`. -/
private def iterSumAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, s => s
  | n + 1, b, s => iterSumAux n (b + (b + 99) / 100) (s + b)

private theorem iterSumAux_eq (n b s : ℕ) :
    iterSumAux n b s = s + ∑ k ∈ Finset.range n, (fun b => b + (b + 99) / 100)^[k] b := by
  induction n generalizing b s with
  | zero => simp [iterSumAux]
  | succ n ih =>
    rw [iterSumAux, ih, Finset.sum_range_succ']
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    omega

private theorem iterSumAux_val : iterSumAux 2212 256 0 = 110065888051444 := by
  decide +kernel

/-- **Early sum of the scales**: `180000 ∑_{j=0}^{2253} b_j ≤ 11 · 2^{41} · 10^{10}`. -/
@[collatz_pos_dens "lem_ck_early_sum"]
theorem scale_early_sum_le :
    180000 * ∑ j ∈ Finset.range 2254, scale j ≤ 11 * 2 ^ 41 * 10 ^ 10 := by
  have hsplit := Finset.sum_range_add scale 42 2212
  have htail : ∑ k ∈ Finset.range 2212, scale (42 + k) = 110065888051444 := by
    simp_rw [scale_42_add]
    have := iterSumAux_eq 2212 256 0
    rw [iterSumAux_val] at this
    omega
  have hhead : ∑ j ∈ Finset.range 42, scale j ≤ 42 * 256 := by
    have := Finset.sum_le_card_nsmul (Finset.range 42) scale 256 (fun j hj =>
      scale_42 ▸ scale_monotone (Finset.mem_range.1 hj).le)
    simpa using this
  rw [show (2254 : ℕ) = 42 + 2212 from rfl, hsplit, htail,
    show (11 * 2 ^ 41 * 10 ^ 10 : ℕ) = 241892558110720000000000 by norm_num]
  generalize ∑ j ∈ Finset.range 42, scale j = s at hhead ⊢
  omega

end CollatzPosDens
