/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Mixing.MxTailStep

/-!
# Large offsets are rare

For every `n ∈ ℕ` and every real `x ≥ 0`, the words `w ∈ ℤ_{≥1}^n` whose offset is at least
`x` have geometric mass at most `7 / (x + 2)`:
$$\mathbf{p}\bigl(\{w \in \mathbb{Z}_{\ge 1}^n : \operatorname{off}(w) \ge x\}\bigr)
  \le \frac{7}{x+2}.$$

## Main results

* `CollatzPosDens.geomMass_offsetTail_le`: the tail bound.
* `CollatzPosDens.le_off_cons_iff`: `off(a v) ≥ x` iff `off(v) ≥ (2^a x - 1) / 3`.

## Implementation notes

The mass is the geometric mass `geomMass` in `ℝ≥0∞`, and the bound `7 / (x + 2)` is the
real number embedded by `ENNReal.ofReal`. The comparison `off(w) ≥ x` is made in `ℝ`, with the
offset cast from `ℚ`.

The bound is proved by induction on `n` for all `x ≥ 0` at once. For `x ≤ 5` it follows from the
total mass `1`; for `x > 5` the first-letter decomposition `geomMass_setOf_length_succ_and`
and `le_off_cons_iff` reduce it to the induction hypothesis at `(2^a x - 1) / 3`, and the
resulting series is bounded by `tailStep_le`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- Prepending a letter `a` turns the condition `off(a v) ≥ x` into
`off(v) ≥ (2^a x - 1) / 3`. -/
theorem le_off_cons_iff (a : ℕ+) (v : Word) (x : ℝ) :
    x ≤ (off (a :: v) : ℝ) ↔ (2 ^ (a : ℕ) * x - 1) / 3 ≤ (off v : ℝ) := by
  rw [off_cons]
  push_cast
  have ht : (0 : ℝ) < 2 ^ (a : ℕ) := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ ht, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  constructor <;> intro h <;> linarith

/-- The words of length `n` have geometric mass at most `1`, so any set of them has mass `≤ 1`. -/
theorem geomMass_setOf_length_and_le_one (n : ℕ) (P : Word → Prop) :
    geomMass {w : Word | w.length = n ∧ P w} ≤ 1 :=
  (geomMass_mono fun _ hw => hw.1).trans (geomMass_setOf_length_eq n).le

/-- The only word of length `0` is `[]`, so no word of length `0` has offset at least `x > 0`. -/
theorem geomMass_setOf_length_zero_and_le_off {x : ℝ} (hx : 0 < x) :
    geomMass {w : Word | w.length = 0 ∧ x ≤ (off w : ℝ)} = 0 := by
  have hempty : {w : Word | w.length = 0 ∧ x ≤ (off w : ℝ)} = ∅ := by
    ext w
    simp only [Set.mem_ofPred_eq, List.length_eq_zero_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl
    simp only [off_nil, Rat.cast_zero, not_le]
    exact hx
  rw [hempty, geomMass_empty]

private lemma inv_two_pow_succ_mul_seven_div_eq {x : ℝ} (hx : 0 ≤ x) (a : ℕ) :
    (2 : ℝ)⁻¹ ^ (a + 1) * (7 / ((2 ^ (a + 1) * x - 1) / 3 + 2)) =
      7 * (3 * ((2 : ℝ)⁻¹ ^ (a + 1) / (2 ^ (a + 1) * x + 5))) := by
  have hu : (0 : ℝ) < 2 ^ (a + 1) := by positivity
  have : (0 : ℝ) < 2 ^ (a + 1) * x + 5 := by positivity
  rw [inv_pow]
  generalize (2 : ℝ) ^ (a + 1) = u at *
  rw [show (u * x - 1) / 3 + 2 = (u * x + 5) / 3 by ring]
  field_simp

/-- **Large offsets are rare.** For every `n ∈ ℕ` and real `x ≥ 0`,
`𝐩({w ∈ ℤ_{≥1}^n : off(w) ≥ x}) ≤ 7 / (x + 2)`. -/
@[collatz_pos_dens "lem_mx_offset_tail"]
theorem geomMass_offsetTail_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    geomMass {w : Word | w.length = n ∧ x ≤ (off w : ℝ)} ≤ ENNReal.ofReal (7 / (x + 2)) := by
  induction n generalizing x with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    rcases le_or_gt x 5 with h5 | h5
    · refine (geomMass_setOf_length_and_le_one _ _).trans ?_
      rw [ENNReal.one_le_ofReal, le_div_iff₀ (by linarith)]
      linarith
  · rw [geomMass_setOf_length_zero_and_le_off (by linarith)]
    exact zero_le
  · have hxa : ∀ a : ℕ+, 0 ≤ (2 ^ (a : ℕ) * x - 1) / 3 := fun a => by
      have : (1 : ℝ) ≤ 2 ^ (a : ℕ) := one_le_pow₀ (by norm_num)
      apply div_nonneg _ (by norm_num)
      nlinarith
    set F : ℕ → ℝ := fun a => (2 : ℝ)⁻¹ ^ a * (7 / ((2 ^ a * x - 1) / 3 + 2)) with hF
    have hFeq : ∀ a : ℕ, F (a + 1) =
        7 * (3 * ((2 : ℝ)⁻¹ ^ (a + 1) / (2 ^ (a + 1) * x + 5))) :=
      fun a => inv_two_pow_succ_mul_seven_div_eq hx a
    obtain ⟨hs, hle⟩ := tailStep_le h5.le
    have hFs : Summable (fun a : ℕ+ => F a) := by
      refine summable_pnat_iff_summable_succ.mpr ?_
      simp_rw [hFeq]
      exact (hs.mul_left 3).mul_left 7
    have hF0 : ∀ a : ℕ+, 0 ≤ F a := fun a => by
      have := hxa a
      simp only [hF]
      positivity
    rw [geomMass_setOf_length_succ_and]
    calc ∑' a : ℕ+, 2⁻¹ ^ (a : ℕ) *
          geomMass {y : Word | y.length = n ∧ x ≤ (off ((a : ℕ+) :: y) : ℝ)}
        ≤ ∑' a : ℕ+, ENNReal.ofReal (F a) := by
          refine ENNReal.tsum_le_tsum fun a => ?_
          simp_rw [le_off_cons_iff]
          have h2 : (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (a : ℕ)) := by
            rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
            simp
          simp only [hF]
          rw [h2, ENNReal.ofReal_mul (by positivity)]
          gcongr
          exact ih (hxa a)
      _ = ENNReal.ofReal (∑' a : ℕ+, F a) := (ENNReal.ofReal_tsum_of_nonneg hF0 hFs).symm
      _ ≤ ENNReal.ofReal (7 / (x + 2)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [tsum_pnat_eq_tsum_succ (f := F)]
          simp_rw [hFeq]
          rw [tsum_mul_left, tsum_mul_left]
          calc 7 * (3 * ∑' a : ℕ, (2 : ℝ)⁻¹ ^ (a + 1) / (2 ^ (a + 1) * x + 5))
              ≤ 7 * (1 / (x + 2)) := by gcongr
            _ = 7 / (x + 2) := by ring

end CollatzPosDens
