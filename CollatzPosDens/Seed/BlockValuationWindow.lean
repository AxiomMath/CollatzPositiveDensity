/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Rb

/-!
# The valuation window of a central block

Let `λ = log₂ 3`. For a level `b`, an overshoot bound `K` and a word `w ∈ 𝒲(b, r_b, K)` of
length `s`, the valuation sum satisfies
$$2b + (s - b)λ - 1 < A(w) < 2b + (s - b)λ + 1 + K.$$
Indeed, with offset `u = r_b` the barrier is `H_{b,r_b}(s) = 2b + B((s-b)₊) - B((b-s)₊)`, and
since `B(j) = ⌈jλ⌉ ∈ [jλ, jλ + 1)` it lies strictly between `2b + (s - b)λ - 1` and
`2b + (s - b)λ + 1`; the crossing condition `H ≤ A(w) ≤ H + K` then gives the window.

## Main results

* `CollatzPosDens.barrier_rb_mem_window`:
  `2b + (s - b)λ - 1 < H_{b,r_b}(s) < 2b + (s - b)λ + 1`.
* `CollatzPosDens.valSum_mem_window_of_mem_firstCrossing_rb`: the window for `A(w)`.

## Implementation notes

The level `b` and the overshoot bound `K` are arbitrary natural numbers; no hypothesis `b ≥ 1`
is needed. The length `s` is `w.length`.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- With offset `u = r_b`, the barrier lies strictly within distance `1` of `2b + (s - b)λ`,
where `λ = log₂ 3`. -/
theorem barrier_rb_mem_window (b s : ℕ) :
    2 * (b : ℝ) + ((s : ℝ) - b) * Real.logb 2 3 - 1 < barrier b (rb b) s ∧
      (barrier b (rb b) s : ℝ) < 2 * (b : ℝ) + ((s : ℝ) - b) * Real.logb 2 3 + 1 := by
  rcases le_total b s with h | h
  · rw [barrier_of_le _ h, add_sub_cancel_right]
    have h1 := mul_logb_le_ceilLog3 (s - b)
    have h2 := ceilLog3_lt_mul_logb_add_one (s - b)
    push_cast [h] at h1 h2 ⊢
    constructor <;> linarith
  · rw [barrier_of_ge _ h, add_sub_cancel_right]
    have h1 := mul_logb_le_ceilLog3 (b - s)
    have h2 := ceilLog3_lt_mul_logb_add_one (b - s)
    push_cast [h] at h1 h2 ⊢
    constructor <;> linarith

/-- **Valuation window of a central block.** A word `w ∈ 𝒲(b, r_b, K)` of length `s` has
`2b + (s - b) log₂ 3 - 1 < A(w) < 2b + (s - b) log₂ 3 + 1 + K`. -/
@[collatz_pos_dens "lem_s05_block_valuation_window"]
theorem valSum_mem_window_of_mem_firstCrossing_rb {b K : ℕ} {w : Word}
    (hw : w ∈ firstCrossing b (rb b) K) :
    2 * (b : ℝ) + ((w.length : ℝ) - b) * Real.logb 2 3 - 1 < w.valSum ∧
      (w.valSum : ℝ) < 2 * (b : ℝ) + ((w.length : ℝ) - b) * Real.logb 2 3 + 1 + K := by
  obtain ⟨h1, h2⟩ := barrier_rb_mem_window b w.length
  have h3 : (barrier b (rb b) w.length : ℝ) ≤ (w.valSum : ℤ) := by
    exact_mod_cast barrier_le_valSum_of_mem_firstCrossing hw
  have h4 : ((w.valSum : ℤ) : ℝ) ≤ (barrier b (rb b) w.length + K : ℤ) := by
    exact_mod_cast valSum_le_barrier_add_of_mem_firstCrossing hw
  push_cast at h3 h4
  constructor <;> linarith

end CollatzPosDens
