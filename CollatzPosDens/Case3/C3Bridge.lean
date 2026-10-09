/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkAlphaBounds
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Case3.C3Row
public import CollatzPosDens.Case3.C3RowBound
public import CollatzPosDens.Case3.C3RowMem

/-!
# A bridge point between two triangles

Let `Δ₀, Δ'` be triangles, `(j₀, l₀) ∈ Δ₀` with `l₀ + g = l_{Δ₀}` for some `g ∈ ℕ`, and
`(j, l) ∈ Δ'` with `l_{Δ₀} ≤ l ≤ l_{Δ₀} + L` and `|j - (j₀ + g / 4)| ≤ J_e`, where
`J_e + α L + 1 ≤ g δ₀`. If `tip(Δ') < l_{Δ₀}`, then the two triangles share a point
`(j_b, l_{Δ₀})` on the row `l_{Δ₀}`, with `j_b ≥ 1`.

The proof takes `j_b = min j ⌊row_{Δ'}(l_{Δ₀})⌋`. It lies in `Δ'` because it is between `j_{Δ'}`
and the row of `Δ'` at `l_{Δ₀}`; it lies in `Δ₀` because `j_b` is within `α L + 1` of `j`, which
is within `J_e` of `j₀ + g / 4`, and the slack `g δ₀ = g (α - 1/4)` absorbs both errors.

## Main results

* `CollatzPosDens.BkTriangle.exists_mem_mem_of_tip_lt`: the bridge point.

## Implementation notes

The real numbers `L` and `J_e` carry no nonnegativity hypotheses: `0 ≤ L` and `0 ≤ J_e`
follow from `l_{Δ₀} ≤ l ≤ l_{Δ₀} + L` and `0 ≤ |j - (j₀ + g / 4)| ≤ J_e`.
-/

@[expose] public section

namespace CollatzPosDens

namespace BkTriangle

/-- A point on the bottom row of `Δ₀` lies in `Δ₀` if it is at most `α g` to the right of a point
`(j₀, l₀) ∈ Δ₀` lying `g` rows above that row. -/
theorem mem_l_of_le_of_sub_le {Δ₀ : BkTriangle} {j₀ l₀ jb : ℤ} {g : ℕ} (h₀ : (j₀, l₀) ∈ Δ₀)
    (hg : l₀ + g = Δ₀.l) (hlo : j₀ ≤ jb) (hup : (jb : ℝ) - j₀ ≤ alpha * g) :
    (jb, Δ₀.l) ∈ Δ₀ := by
  obtain ⟨hj₀, -, hw₀⟩ := h₀
  simp only [bkJ, bkL] at hj₀ hw₀
  have hgl : ((Δ₀.l - l₀ : ℤ) : ℝ) = g := by
    rw [← hg]
    push_cast
    ring
  rw [hgl] at hw₀
  refine ⟨hj₀.trans hlo, le_rfl, ?_⟩
  simp only [bkJ, bkL, sub_self, Int.cast_zero, zero_mul, add_zero]
  push_cast at hw₀ ⊢
  have : ((jb : ℝ) - j₀) * Real.log 9 ≤ g * Real.log 2 := by
    rw [← alpha_mul_log_nine, mul_comm alpha, ← mul_assoc, mul_comm (g : ℝ), mul_assoc,
      mul_comm (g : ℝ), ← mul_assoc, mul_comm (Real.log 9)]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 9)]
  nlinarith

/-- Let `(j₀, l₀) ∈ Δ₀` with `l₀ + g = l_{Δ₀}` and `(j, l) ∈ Δ'` with `l_{Δ₀} ≤ l ≤ l_{Δ₀} + L`
and `|j - (j₀ + g / 4)| ≤ J_e`. If `J_e + α L + 1 ≤ g δ₀` and `tip(Δ') < l_{Δ₀}`, then some
`(j_b, l_{Δ₀})` with `j_b ≥ 1` lies in both `Δ₀` and `Δ'`. -/
@[collatz_pos_dens "lem_c3_bridge"]
theorem exists_mem_mem_of_tip_lt {Δ₀ Δ' : BkTriangle} {j₀ l₀ j l : ℤ} {g : ℕ} {L Je : ℝ}
    (h₀ : (j₀, l₀) ∈ Δ₀) (hg : l₀ + g = Δ₀.l) (h' : (j, l) ∈ Δ') (hl₁ : Δ₀.l ≤ l)
    (hl₂ : (l : ℝ) ≤ Δ₀.l + L) (hj : |(j : ℝ) - (j₀ + g / 4)| ≤ Je)
    (hE : Je + alpha * L + 1 ≤ g * drift) (htip : Δ'.tip < Δ₀.l) :
    ∃ jb : ℤ, 1 ≤ jb ∧ (jb, Δ₀.l) ∈ Δ₀ ∧ (jb, Δ₀.l) ∈ Δ' := by
  have hαpos := alpha_pos
  set ρ := Δ'.row Δ₀.l with hρ
  have hρj : (Δ'.j : ℝ) ≤ ρ := by
    rw [hρ, row_def]
    nlinarith [Real.log_pos one_lt_two, Real.log_pos (by norm_num : (1 : ℝ) < 9),
      alpha_mul_log_nine]
  have hjρ : (j : ℝ) ≤ ρ + alpha * ((l : ℝ) - Δ₀.l) := by
    have hb := row_bound_of_mem h'
    simp only [bkJ, bkL] at hb
    push_cast at hb
    have : ((j : ℝ) - Δ'.j) ≤ alpha * ((l : ℝ) - Δ'.tip) := by
      rw [← mul_le_mul_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 9)), mul_assoc,
        mul_comm _ (Real.log 9), ← mul_assoc, mul_comm alpha, mul_assoc, mul_comm (Real.log 9),
        alpha_mul_log_nine]
      linarith
    rw [hρ, row_def]
    linarith
  have hL : (0 : ℝ) ≤ L := by linarith [(Int.cast_le.2 hl₁ : ((Δ₀.l : ℤ) : ℝ) ≤ l)]
  set jb := min j ⌊ρ⌋ with hjb
  have hjb_le_ρ : (jb : ℝ) ≤ ρ := (Int.cast_le.2 (min_le_right _ _)).trans (Int.floor_le ρ)
  have hjjb : (j : ℝ) - jb ≤ alpha * L + 1 := by
    rcases min_choice j ⌊ρ⌋ with h | h
    · rw [hjb, h]
      nlinarith
    · rw [hjb, h]
      have := Int.lt_floor_add_one ρ
      have : alpha * ((l : ℝ) - Δ₀.l) ≤ alpha * L :=
        mul_le_mul_of_nonneg_left (by linarith) hαpos.le
      linarith
  have hgδ : (g : ℝ) * drift ≤ g / 4 := by
    rw [drift_def]
    nlinarith [(Nat.cast_nonneg g : (0 : ℝ) ≤ g), alpha_le_two_div_five]
  have hjabs := abs_le.1 hj
  have hjb_ge₀ : j₀ ≤ jb := by exact_mod_cast (by linarith : (j₀ : ℝ) ≤ jb)
  have hjb_up : (jb : ℝ) - j₀ ≤ alpha * g := by
    have : (jb : ℝ) ≤ j := Int.cast_le.2 (min_le_left _ _)
    have hd : (g : ℝ) * drift = alpha * g - g / 4 := by
      rw [drift_def]
      ring
    nlinarith
  exact ⟨jb, Δ₀.one_le_j.trans (h₀.1.trans hjb_ge₀), mem_l_of_le_of_sub_le h₀ hg hjb_ge₀ hjb_up,
    Δ'.mem_of_le_row (hl₁.trans (le_l_of_mem h')) (le_min (j_le_of_mem h') (Int.le_floor.2 hρj))
      hjb_le_ρ⟩

end BkTriangle

end CollatzPosDens
