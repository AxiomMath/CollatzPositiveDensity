/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnListHorMgf
public import CollatzPosDens.Renewal.RnMgfSixteenth

/-!
# Horizontal tail of hold lists

For `P ∈ ℕ` and real `m`, the product law `η^{⊗P}` gives mass at most `exp (P/2 - m/160)` to the
hold lists `h ∈ 𝒫^P` with `m ≤ 10 (j(h_1) + ⋯ + j(h_P))`.

On that range `1 ≤ exp ((∑_i j(h_i) - m/10) / 16)`, so the sum is at most
`e^{-m/160} ∑_{h ∈ 𝒫^P} η^{⊗P}(h) e^{∑_i j(h_i) / 16} = e^{-m/160} M₄₅(1/16)^P`, and
`M₄₅(1/16) ≤ 5/4 ≤ 1 + 1/2 ≤ e^{1/2}`.

## Main results

* `CollatzPosDens.tsum_holdListLaw_horTail_le`: the bound, as a sum in `[0, ∞]`.

## Implementation notes

The set `𝒫^P` is the set of tuples `h : Fin P → ℕ × ℤ` with `1 ≤ j(h_i)` for every `i`, and the
summation range is the subtype of those which moreover satisfy `m ≤ 10 ∑_i j(h_i)`. The main
statement is a sum in `ℝ≥0∞` of the nonnegative weights; since the bound is finite it also records
convergence.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- `5/4 ≤ e^{1/2}`. -/
private lemma five_div_four_le_exp_half : (5 / 4 : ℝ≥0∞) ≤ ENNReal.ofReal (exp (1 / 2)) := by
  calc (5 / 4 : ℝ≥0∞) = ENNReal.ofReal (5 / 4) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (exp (1 / 2)) :=
        ENNReal.ofReal_le_ofReal (by linarith [add_one_le_exp (1 / 2 : ℝ)])

/-- **Horizontal tail of hold lists.** For `P ∈ ℕ` and real `m`,
`∑ η^{⊗P}(h) ≤ exp (P/2 - m/160)`, the sum (in `[0, ∞]`) over `h ∈ 𝒫^P` with
`m ≤ 10 (j(h_1) + ⋯ + j(h_P))`. -/
@[collatz_pos_dens "lem_rn_list_hor_tail"]
theorem tsum_holdListLaw_horTail_le (P : ℕ) (m : ℝ) :
    ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ m ≤ 10 * ∑ i, ((h i).1 : ℝ)},
      ENNReal.ofReal (holdListLaw h.1) ≤ ENNReal.ofReal (exp (P / 2 - m / 160)) := by
  set F : (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun h ↦
    ENNReal.ofReal (holdListLaw h * exp (1 / 16 * ∑ i, ((h i).1 : ℝ))) with hF
  have hpt : ∀ h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ m ≤ 10 * ∑ i, ((h i).1 : ℝ)},
      ENNReal.ofReal (holdListLaw h.1) ≤ ENNReal.ofReal (exp (-(m / 160))) * F h.1 := by
    intro h
    rw [hF, ← ENNReal.ofReal_mul (exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_left_comm]
    refine le_mul_of_one_le_right (holdListLaw_nonneg _) ?_
    rw [← exp_add, one_le_exp_iff]
    linarith [h.2.2]
  have hsub : ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ m ≤ 10 * ∑ i, ((h i).1 : ℝ)},
      F h.1 ≤ ∑' h : {h : Fin P → ℕ × ℤ // ∀ i, 1 ≤ (h i).1}, F h.1 :=
    ENNReal.tsum_comp_le_tsum_of_injective (f := fun h : {h : Fin P → ℕ × ℤ //
        (∀ i, 1 ≤ (h i).1) ∧ m ≤ 10 * ∑ i, ((h i).1 : ℝ)} ↦
        (⟨h.1, h.2.1⟩ : {h : Fin P → ℕ × ℤ // ∀ i, 1 ≤ (h i).1}))
      (fun a b hab ↦ Subtype.ext (congrArg Subtype.val hab :)) (fun h ↦ F h.1)
  calc _ ≤ ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ m ≤ 10 * ∑ i, ((h i).1 : ℝ)},
          ENNReal.ofReal (exp (-(m / 160))) * F h.1 := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (exp (-(m / 160))) *
          ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ m ≤ 10 * ∑ i, ((h i).1 : ℝ)},
            F h.1 := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (exp (-(m / 160))) * mgfNu45 (1 / 16) ^ P := by
        gcongr
        exact hsub.trans_eq (tsum_holdListLaw_mul_exp P (1 / 16))
    _ ≤ ENNReal.ofReal (exp (-(m / 160))) * ENNReal.ofReal (exp (1 / 2)) ^ P := by
        gcongr
        exact mgfNu45_one_div_sixteen_le.trans five_div_four_le_exp_half
    _ = ENNReal.ofReal (exp (P / 2 - m / 160)) := by
        rw [← ENNReal.ofReal_pow (exp_pos _).le, ← ENNReal.ofReal_mul (exp_pos _).le,
          ← exp_nat_mul, ← exp_add]
        ring_nf

end CollatzPosDens
