/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Terminal.S06ClipFloor

/-!
# Loss below the degree floor

For every `m ∈ ℕ` and every real `B > 0`, the words of length `m` whose valuation sum is below
the clipping degree floor `A = A^clp_{m,B}` have small geometric mass:
$$\mathbf p(\{u \in ℤ_{≥1}^m : A(u) < A\}) < 8 / B.$$
Indeed `A(u) ≤ A - 1` gives `2^{-A(u)} ≤ 2^{A-1} 4^{-A(u)}`, the sum
`∑_{u ∈ ℤ_{≥1}^m} 4^{-A(u)} = (∑_{a ≥ 1} 4^{-a})^m = 3^{-m}` factorises over the letters, and
`2^{A-1} 3^{-m} < 8 / B` because `A - 1 < log₂(8 · 3^m / B)`.

## Main results

* `CollatzPosDens.tsum_four_inv_pow_valSum_setOf_length`:
  `∑_{u ∈ ℤ_{≥1}^t} 4^{-A(u)} = 3^{-t}`.
* `CollatzPosDens.geomMass_valSum_lt_clipFloor_lt`: the loss bound above.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- `∑_{a ≥ 1} 4^{-a} = 1/3` in `ℝ≥0∞`. -/
theorem tsum_four_inv_pow_pnat : ∑' a : ℕ+, (4⁻¹ : ℝ≥0∞) ^ (a : ℕ) = 3⁻¹ := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n => (4⁻¹ : ℝ≥0∞) ^ n)]
  have h : ∀ n : ℕ, (4⁻¹ : ℝ≥0∞) ^ (n + 1) = ENNReal.ofReal ((1 / 4 : ℝ) ^ (n + 1)) := by
    intro n
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  simp_rw [h]
  have hsum : Summable fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 4 : ℝ) < 1)).comp_injective
      (add_left_injective 1)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  have hs : ∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) = 1 / 3 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [hs, one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- The sum of `4^{-A(u)}` over the words of length `t` factorises:
`∑_{u ∈ ℤ_{≥1}^t} 4^{-A(u)} = (∑_{a ≥ 1} 4^{-a})^t = 3^{-t}`. -/
theorem tsum_four_inv_pow_valSum_setOf_length (t : ℕ) :
    ∑' w : {w : Word | w.length = t}, (4⁻¹ : ℝ≥0∞) ^ (w : Word).valSum = 3⁻¹ ^ t := by
  induction t with
  | zero =>
    rw [show {w : Word | w.length = 0} = {[]} by ext; simp]
    simp
  | succ t ih =>
    rw [Word.tsum_setOf_length_succ t fun w => (4⁻¹ : ℝ≥0∞) ^ w.valSum]
    simp only [Word.valSum_cons, pow_add, ENNReal.tsum_mul_left]
    rw [ih, ENNReal.tsum_mul_right, tsum_four_inv_pow_pnat]
    ring

/-- `2^{A^clp_{m,B} - 1} 3^{-m} < 8 / B` for `B > 0`. -/
theorem two_zpow_clipFloor_sub_one_div_three_pow_lt (m : ℕ) {B : ℝ} (hB : 0 < B) :
    (2 : ℝ) ^ (clipFloor m B - 1) / 3 ^ m < 8 / B := by
  have hpos : (0 : ℝ) < 8 * 3 ^ m / B := by positivity
  have h1 : ((clipFloor m B - 1 : ℤ) : ℝ) < Real.logb 2 (8 * 3 ^ m / B) := by
    have := Int.ceil_lt_add_one (Real.logb 2 (8 * 3 ^ m / B))
    rw [← clipFloor_def] at this
    push_cast
    linarith
  rw [Real.lt_logb_iff_rpow_lt one_lt_two hpos, Real.rpow_intCast] at h1
  rw [div_lt_iff₀ (by positivity)]
  calc (2 : ℝ) ^ (clipFloor m B - 1) < 8 * 3 ^ m / B := h1
    _ = 8 / B * 3 ^ m := by ring

/-- **Loss below the degree floor.** For every `m ∈ ℕ` and real `B > 0`,
`𝐩({u ∈ ℤ_{≥1}^m : A(u) < A^clp_{m,B}}) < 8 / B`. -/
@[collatz_pos_dens "lem_s06_clip_floor_loss"]
theorem geomMass_valSum_lt_clipFloor_lt (m : ℕ) {B : ℝ} (hB : 0 < B) :
    geomMass {u : Word | u.length = m ∧ (u.valSum : ℤ) < clipFloor m B} <
      ENNReal.ofReal (8 / B) := by
  set A := clipFloor m B
  set C : ℝ := (2 : ℝ) ^ (A - 1)
  have hC : 0 < C := zpow_pos two_pos _
  have hterm : ∀ w : {w : Word | w.length = m},
      {x : Word | (x.valSum : ℤ) < A}.indicator Word.massWeight w ≤
        ENNReal.ofReal C * (4⁻¹ : ℝ≥0∞) ^ (w : Word).valSum := by
    intro w
    by_cases hw : ((w : Word).valSum : ℤ) < A
    · rw [Set.indicator_of_mem (s := {x : Word | (x.valSum : ℤ) < A}) hw, Word.massWeight]
      have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
      have h4 : (4⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
      rw [h2, h4, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
        ← ENNReal.ofReal_mul hC.le]
      refine ENNReal.ofReal_le_ofReal ?_
      set v := (w : Word).valSum
      have hv : (v : ℤ) ≤ A - 1 := by omega
      have hCv : (2 : ℝ) ^ v ≤ C := by
        rw [← zpow_natCast]
        exact zpow_le_zpow_right₀ one_le_two hv
      have hq : (1 / 4 : ℝ) ^ v = (1 / 2) ^ v * (1 / 2) ^ v := by
        rw [← mul_pow]; norm_num
      have h1 : (1 : ℝ) ≤ C * (1 / 2) ^ v := by
        rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        exact hCv
      rw [hq, ← mul_assoc]
      nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) v]
    · rw [Set.indicator_of_notMem (s := {x : Word | (x.valSum : ℤ) < A}) hw]
      exact zero_le
  rw [geomMass_setOf_length_and]
  calc _ ≤ ∑' w : {w : Word | w.length = m},
        ENNReal.ofReal C * (4⁻¹ : ℝ≥0∞) ^ (w : Word).valSum := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C / 3 ^ m) := by
      rw [ENNReal.tsum_mul_left, tsum_four_inv_pow_valSum_setOf_length, div_eq_mul_inv,
        ENNReal.ofReal_mul hC.le, ← inv_pow, ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    _ < ENNReal.ofReal (8 / B) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
        (two_zpow_clipFloor_sub_one_div_three_pow_lt m hB)

end CollatzPosDens
