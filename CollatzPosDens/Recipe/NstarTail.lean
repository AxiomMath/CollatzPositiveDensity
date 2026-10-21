/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhEj
public import CollatzPosDens.Recipe.PhEjGeometric
public import CollatzPosDens.Recipe.TailMargin
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The propagation tail after the generation threshold

Let `E_j` be the propagation majorant, `N_*` the generation threshold and `θ_tl` the tail
margin. Then for every `n`,
$$\sum_{j=N_*}^{n-1} \mathsf E_j < \theta_{\mathrm{tl}}.$$

By the geometric majorant
`E_j ≤ (7584/10^6) ρ^{j-N_*} + 2^{-90} σ^{j-N_*}`, with `ρ = 990945/10^6` and `σ = 199/200`,
and the finite geometric sums `∑_{i<M} r^i ≤ 1/(1-r)` for `0 ≤ r < 1`, the partial sums are at
most `(7584/10^6) · 200000/1811 + 200 · 2^{-90} = 7584/9055 + 200 · 2^{-90} = 0.837548…`.
This is less than `6/7`, by the exact integer comparison `200 · 63385 < 1242 · 2^{90}` (note
`6/7 - 7584/9055 = 1242/63385`), and `6/7 ≤ θ_tl`.

## Main results

* `CollatzPosDens.sum_Ico_generationThreshold_propagationMajorant_lt`:
  `∑_{j=N_*}^{n-1} E_j < θ_tl` for every `n`.

## Implementation notes

The statement holds for every `n`, not only for `n ≥ N_*`: for `n ≤ N_*` the sum is empty.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `0 ≤ r < 1`, `∑_{j=N}^{n-1} r^{j-N} ≤ 1/(1-r)`. -/
private lemma sum_Ico_pow_sub_le {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) (N n : ℕ) :
    ∑ j ∈ Finset.Ico N n, r ^ (j - N) ≤ 1 / (1 - r) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  rw [Finset.range_eq_Ico]
  simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := n - N) hr₀ hr₁

/-- `∑_{j=N_*}^{n-1} E_j < 6/7` for every `n`. -/
private lemma sum_Ico_generationThreshold_propagationMajorant_lt_six_sevenths (n : ℕ) :
    ∑ j ∈ Finset.Ico generationThreshold n, propagationMajorant j < 6 / 7 := by
  have hsum := Finset.sum_le_sum (s := Finset.Ico generationThreshold n)
    fun j hj => propagationMajorant_le_geometric (Finset.mem_Ico.1 hj).1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hρ := sum_Ico_pow_sub_le (r := 990945 / 10 ^ 6) (by norm_num) (by norm_num)
    generationThreshold n
  have hσ := sum_Ico_pow_sub_le (r := 199 / 200) (by norm_num) (by norm_num)
    generationThreshold n
  have h90 : (0 : ℝ) < 2 ^ (-90 : ℤ) := by positivity
  have hcert : (200 * 63385 : ℕ) < 1242 * 2 ^ 90 := by decide +kernel
  have hR : (200 : ℝ) * 63385 < 1242 * 2 ^ 90 := by exact_mod_cast hcert
  have h2 : (200 : ℝ) * 2 ^ (-90 : ℤ) < 1242 / 63385 := by
    rw [zpow_neg, zpow_ofNat, lt_div_iff₀ (by norm_num), mul_assoc, mul_comm _ (63385 : ℝ),
      ← mul_assoc, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
    linarith
  have hρ' : (7584 / 10 ^ 6 : ℝ) * ∑ j ∈ Finset.Ico generationThreshold n,
      (990945 / 10 ^ 6 : ℝ) ^ (j - generationThreshold) ≤ 7584 / 9055 := by
    calc _ ≤ (7584 / 10 ^ 6 : ℝ) * (1 / (1 - 990945 / 10 ^ 6)) := by gcongr
      _ = 7584 / 9055 := by norm_num
  have hσ' : (2 : ℝ) ^ (-90 : ℤ) * ∑ j ∈ Finset.Ico generationThreshold n,
      (199 / 200 : ℝ) ^ (j - generationThreshold) ≤ 200 * 2 ^ (-90 : ℤ) := by
    calc _ ≤ (2 : ℝ) ^ (-90 : ℤ) * (1 / (1 - 199 / 200)) := by gcongr
      _ = 200 * 2 ^ (-90 : ℤ) := by norm_num
  have : (7584 / 9055 : ℝ) + 1242 / 63385 = 6 / 7 := by norm_num
  linarith

/-- **Tail after `N_*`.** For every `n`, `∑_{j=N_*}^{n-1} E_j < θ_tl`. -/
@[collatz_pos_dens "lem_Nstar_tail"]
theorem sum_Ico_generationThreshold_propagationMajorant_lt (n : ℕ) :
    ∑ j ∈ Finset.Ico generationThreshold n, propagationMajorant j < (tailMargin : ℝ) := by
  refine (sum_Ico_generationThreshold_propagationMajorant_lt_six_sevenths n).trans_le ?_
  have h : (6 / 7 : ℚ) ≤ tailMargin := by norm_num [tailMargin_def]
  calc (6 / 7 : ℝ) = ((6 / 7 : ℚ) : ℝ) := by norm_num
    _ ≤ (tailMargin : ℝ) := Rat.cast_le.2 h

end CollatzPosDens
