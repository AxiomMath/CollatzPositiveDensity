/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkAlphaBounds

/-!
# The triangle margin at a far gap

Let `P ≥ 1` and `0 ≤ v ≤ P - 1` be integers and let `G` be a real number with `G ≥ 2 ^ 36 P`. Then
$$2 G^{3/5} + 272 \, \alpha \, (v + 1) + 1 \le G \, \delta_0 .$$
Indeed `δ₀ = α - 1 / 4 ≥ 1 / 16` and `α ≤ 2 / 5`; since `G ≥ 2 ^ 20` we have
`2 G^{3/5} ≤ G / 128`, and `272 α (v + 1) + 1 ≤ (544 / 5) P + P ≤ G / 32`.

## Main results

* `CollatzPosDens.two_mul_rpow_add_alpha_mul_add_one_le_mul_drift`: if `v + 1 ≤ P` and
  `2 ^ 36 P ≤ G`, then `2 G ^ (3 / 5) + 272 α (v + 1) + 1 ≤ G δ₀`.

## Implementation notes

The integers `P` and `v` are taken in `ℕ`, which encodes `0 ≤ v`; the two hypotheses `P ≥ 1` and
`v ≤ P - 1` are combined into the single hypothesis `v + 1 ≤ P`, which is equivalent to them.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `G ≥ 2 ^ 20` then `G ^ (3 / 5) ≤ G / 256`. -/
private lemma rpow_three_div_five_le_div_of_le {G : ℝ} (hG : 2 ^ 20 ≤ G) :
    G ^ ((3 : ℝ) / 5) ≤ G / 256 := by
  have hpos : 0 < G := lt_of_lt_of_le (by norm_num) hG
  have G0 : 0 ≤ G := hpos.le
  have h5 : (G ^ ((2 : ℝ) / 5)) ^ 5 = G ^ 2 := by
    rw [← Real.rpow_mul_natCast G0]
    norm_num
  have h256 : (256 : ℝ) ≤ G ^ ((2 : ℝ) / 5) := by
    have hb : (256 : ℝ) ^ 5 ≤ (G ^ ((2 : ℝ) / 5)) ^ 5 := by
      rw [h5]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) (Real.rpow_nonneg G0 _) (by norm_num)).1 hb
  have hsplit : G ^ ((3 : ℝ) / 5) * G ^ ((2 : ℝ) / 5) = G := by
    rw [← Real.rpow_add hpos]
    norm_num
  have h3 : 0 ≤ G ^ ((3 : ℝ) / 5) := Real.rpow_nonneg G0 _
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- **The triangle margin at a far gap**: if `v + 1 ≤ P` (that is, `P ≥ 1` and `0 ≤ v ≤ P - 1`)
and `G ≥ 2 ^ 36 P`, then `2 G ^ (3 / 5) + 272 α (v + 1) + 1 ≤ G δ₀`. -/
@[collatz_pos_dens "lem_c3_margin"]
theorem two_mul_rpow_add_alpha_mul_add_one_le_mul_drift {P v : ℕ} {G : ℝ} (hv : v + 1 ≤ P)
    (hG : 2 ^ 36 * (P : ℝ) ≤ G) :
    2 * G ^ ((3 : ℝ) / 5) + 272 * alpha * ((v : ℝ) + 1) + 1 ≤ G * drift := by
  have hvR : (v : ℝ) + 1 ≤ P := by exact_mod_cast hv
  have hP1 : (1 : ℝ) ≤ P := by linarith [v.cast_nonneg (α := ℝ)]
  have hr := rpow_three_div_five_le_div_of_le (G := G) (by nlinarith)
  have hd : (1 : ℝ) / 16 ≤ drift := by
    rw [drift_def]
    linarith [five_div_sixteen_le_alpha]
  have hG0 : 0 ≤ G := by nlinarith
  have hα0 : 0 ≤ alpha := by linarith [five_div_sixteen_le_alpha]
  have hαv : alpha * ((v : ℝ) + 1) ≤ 2 / 5 * P :=
    mul_le_mul alpha_le_two_div_five hvR (by positivity) (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hd hG0]

end CollatzPosDens
