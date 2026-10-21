/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapFactor

/-!
# Retained factors along a suffix word

For an integer `h`, a real `z` and a finite word `u = (u_1, …, u_K)` of integers, the weight
`wt_h(z; u)` is defined by recursion on `K`: `wt_h(z; u) = 1` if `K = 0` or `h ≥ 15`, and for
`K ≥ 1` and `h ≤ 14`, with `d = u_1` and `u⁻ = (u_2, …, u_K)`,
`wt_h(z; u) = A · G`, where `A = Φ^cap_d(z / 2^{h+d})` if `d ≤ 17 - h` and `A = 1` otherwise,
and `G = wt_{h+d}(9z; u⁻)` if `d ∉ {4, 5}` and `h + d ≤ 15`, and `G = 1` otherwise. Here
`Φ^cap` is the capped packet factor `CollatzPosDens.trCapFactor`. The weight is the product of
the capped packet factors retained along the word, and lies in `(0, 1]`.

## Main definitions

* `CollatzPosDens.c3H17Weight`: the weight `wt_h(z; u)`.

## Main results

* `CollatzPosDens.c3H17Weight_nil`: `wt_h(z; ()) = 1`.
* `CollatzPosDens.c3H17Weight_of_le`: `wt_h(z; u) = 1` for `h ≥ 15`.
* `CollatzPosDens.c3H17Weight_cons_of_lt`: the recursion for `h < 15`.
* `CollatzPosDens.c3H17Weight_pos`, `CollatzPosDens.c3H17Weight_le_one`: `0 < wt_h(z; u) ≤ 1`.

## Implementation notes

The word is a `List ℤ` and the definition is by structural recursion on it. The index `h`
ranges over all of `ℤ`, and the same recursion is used for `h ≤ 0`, although only `h ≥ 1` is of
interest.
-/

@[expose] public section

namespace CollatzPosDens

/-- The retained factors along a suffix word: `wt_h(z; ()) = 1`, `wt_h(z; u) = 1` for `h ≥ 15`,
and for `h ≤ 14`, `wt_h(z; d :: u⁻) = A · G` with `A = Φ^cap_d(z / 2^{h+d})` if `d ≤ 17 - h`
(and `A = 1` otherwise), and `G = wt_{h+d}(9z; u⁻)` if `d ∉ {4, 5}` and `h + d ≤ 15` (and
`G = 1` otherwise). -/
@[collatz_pos_dens "def_c3_h17_weight"]
noncomputable def c3H17Weight : ℤ → ℝ → List ℤ → ℝ
  | _, _, [] => 1
  | h, z, d :: u =>
    if 15 ≤ h then 1
    else
      (if d ≤ 17 - h then trCapFactor d (z / (2 : ℝ) ^ (h + d)) else 1) *
        if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Weight (h + d) (9 * z) u else 1

/-- The weight of the empty word is `1`. -/
@[simp]
theorem c3H17Weight_nil (h : ℤ) (z : ℝ) : c3H17Weight h z [] = 1 := by
  rw [c3H17Weight]

/-- The weight is `1` when `h ≥ 15`. -/
theorem c3H17Weight_of_le {h : ℤ} (hh : 15 ≤ h) (z : ℝ) (u : List ℤ) :
    c3H17Weight h z u = 1 := by
  cases u with
  | nil => rfl
  | cons d u => rw [c3H17Weight, ite_eq_left_of_eq_true _ _ (eq_true hh)]

/-- The recursion defining `wt_h(z; u)` for `h < 15` and a nonempty word. -/
theorem c3H17Weight_cons_of_lt {h : ℤ} (hh : h < 15) (z : ℝ) (d : ℤ) (u : List ℤ) :
    c3H17Weight h z (d :: u) =
      (if d ≤ 17 - h then trCapFactor d (z / (2 : ℝ) ^ (h + d)) else 1) *
        if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Weight (h + d) (9 * z) u else 1 := by
  rw [c3H17Weight, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hh))]

/-- The weight is positive and at most `1`. -/
theorem c3H17Weight_mem_Ioc (h : ℤ) (z : ℝ) (u : List ℤ) :
    c3H17Weight h z u ∈ Set.Ioc 0 1 := by
  induction u generalizing h z with
  | nil => simp
  | cons d u ih =>
    rcases le_or_gt 15 h with hh | hh
    · rw [c3H17Weight_of_le hh]
      simp
    rw [c3H17Weight_cons_of_lt hh]
    have hA : (if d ≤ 17 - h then trCapFactor d (z / (2 : ℝ) ^ (h + d)) else 1) ∈ Set.Ioc 0 1 := by
      split_ifs
      · exact ⟨trCapFactor_pos _ _, trCapFactor_le_one _ _⟩
      · simp
    have hG : (if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Weight (h + d) (9 * z) u
        else 1) ∈ Set.Ioc 0 1 := by
      split_ifs
      · exact ih _ _
      · simp
    exact ⟨mul_pos hA.1 hG.1, (mul_le_mul hA.2 hG.2 hG.1.le zero_le_one).trans_eq (one_mul 1)⟩

/-- The weight is positive. -/
theorem c3H17Weight_pos (h : ℤ) (z : ℝ) (u : List ℤ) : 0 < c3H17Weight h z u :=
  (c3H17Weight_mem_Ioc h z u).1

/-- The weight is nonnegative. -/
theorem c3H17Weight_nonneg (h : ℤ) (z : ℝ) (u : List ℤ) : 0 ≤ c3H17Weight h z u :=
  (c3H17Weight_pos h z u).le

/-- The weight is at most `1`. -/
theorem c3H17Weight_le_one (h : ℤ) (z : ℝ) (u : List ℤ) : c3H17Weight h z u ≤ 1 :=
  (c3H17Weight_mem_Ioc h z u).2

end CollatzPosDens
