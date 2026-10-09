/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldWords
public import CollatzPosDens.Renewal.RnHoldFinite
public import CollatzPosDens.Renewal.RnVpgf
public import CollatzPosDens.Renewal.RnPascal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Value of the vertical generating function of a hold

For real `0 < y < 2` with `y² / (2 - y)² - (3/16) y⁴ - (1/8) y⁵ < 1`, the vertical generating
function `𝖵(y) = ∑_{(j, l) ∈ 𝒫} η(j, l) y^l` has the finite value
`𝖵(y) = Σ_cl / (1 - Σ_nc)`, where `Σ_cl = ϖ(4) y⁴ + ϖ(5) y⁵ = (3/16) y⁴ + (1/8) y⁵` is the
weight of a closing letter and `Σ_nc = ∑_{b ∉ {4, 5}} ϖ(b) y^b = y² / (2 - y)² - Σ_cl` is the
weight of a non-closing letter.

The proof writes `y^l = ∏ᵢ y^{cᵢ}` for a hold word `c ∈ 𝒞_{j,l}`, sums over `l` first (Tonelli),
so that the words of length `j` contribute `Σ_nc^{j-1} Σ_cl`, and sums the geometric series in
`j`. The total weight `∑_b ϖ(b) y^b = ∑_{n ≥ 0} (n + 1) x^{n+2} = x² / (1 - x)²` with
`x = y / 2` gives the value of `Σ_nc`.

## Main results

* `CollatzPosDens.holdVpgf_eq`: the closed form of `𝖵(y)`.
* `CollatzPosDens.holdVpgf_ne_top`: under the same hypotheses, `𝖵(y) ≠ ∞`.

## Implementation notes

All sums are carried out in `[0, ∞]`, where Tonelli's theorem and the geometric series hold
without summability side conditions; the closed form is stated as the `ENNReal.ofReal` of the
real value, which in particular shows that the series is finite.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal
open Finset

/-- The `[0, ∞]`-valued weight `ϖ(b) y^b` of a single letter `b`. -/
private noncomputable def letterWt (y : ℝ) (b : ℤ) : ℝ≥0∞ := ENNReal.ofReal (varpi b * y ^ b)

private lemma letterWt_of_lt_two {y : ℝ} {b : ℤ} (hb : ¬ 2 ≤ b) : letterWt y b = 0 := by
  rw [letterWt, varpi_of_le_one (by omega), zero_mul, ENNReal.ofReal_zero]

private lemma zpow_sum_of_pos {y : ℝ} (hy : 0 < y) {j : ℕ} (c : Fin j → ℤ) :
    y ^ (∑ i, c i) = ∏ i, y ^ c i := by
  rw [← Real.rpow_intCast]
  push_cast
  rw [Real.rpow_sum_of_pos hy]
  simp [Real.rpow_intCast]

/-- One term of `𝖵(y)` as a sum over hold words. -/
private lemma term_eq {y : ℝ} (hy : 0 < y) (j : ℕ) (l : ℤ) :
    ENNReal.ofReal (holdLaw j l * y ^ l) =
      ∑' c : Fin j → ℤ, (holdWords j l).indicator (fun c ↦ ∏ i, letterWt y (c i)) c := by
  have := (holdWords_finite j l).to_subtype
  rw [holdLaw_def, ← tsum_mul_right,
    ENNReal.ofReal_tsum_of_nonneg (fun c ↦ mul_nonneg
      (prod_nonneg fun _ _ ↦ varpi_nonneg _) (zpow_nonneg hy.le _)) (Summable.of_finite),
    ← tsum_subtype (holdWords j l) (fun c ↦ ∏ i, letterWt y (c i))]
  refine tsum_congr fun ⟨c, hc⟩ ↦ ?_
  dsimp only
  rw [← holdWords_sum_eq hc, zpow_sum_of_pos hy, ← prod_mul_distrib,
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ mul_nonneg (varpi_nonneg _) (zpow_nonneg hy.le _)]
  rfl

/-- Summing over the letter sum `l` first. -/
private lemma sum_l_eq {y : ℝ} (hy : 0 < y) (j : ℕ) :
    ∑' l : ℤ, ENNReal.ofReal (holdLaw j l * y ^ l) =
      ∑' c : Fin j → ℤ,
        (holdWords j (∑ i, c i)).indicator (fun c ↦ ∏ i, letterWt y (c i)) c := by
  simp_rw [term_eq hy]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun c ↦ tsum_eq_single _ fun l hl ↦
    Set.indicator_of_notMem (fun h ↦ hl (holdWords_sum_eq h).symm) _

private lemma mem_holdWords_cons {m : ℕ} (a : ℤ) (c : Fin (m + 1) → ℤ) :
    (Fin.cons a c : Fin (m + 2) → ℤ) ∈ holdWords (m + 2) (∑ i, (Fin.cons a c : Fin (m + 2) → ℤ) i)
      ↔ (2 ≤ a ∧ a ∉ ({4, 5} : Set ℤ)) ∧ c ∈ holdWords (m + 1) (∑ i, c i) := by
  rw [mem_holdWords, mem_holdWords (c := c)]
  constructor
  · rintro ⟨h2, hlt, heq, -⟩
    refine ⟨⟨by simpa using h2 0, by simpa using hlt 0 (by simp only [Fin.val_zero]; omega)⟩,
      fun i ↦ by simpa using h2 i.succ,
      fun i hi ↦ by simpa using hlt i.succ (by simp only [Fin.val_succ]; omega),
      fun i hi ↦ by simpa using heq i.succ (by simp only [Fin.val_succ]; omega), rfl⟩
  · rintro ⟨⟨ha2, ha45⟩, h2, hlt, heq, -⟩
    refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, fun i hi ↦ ?_, rfl⟩
    · cases i using Fin.cases with
      | zero => simpa using ha2
      | succ i => simpa using h2 i
    · cases i using Fin.cases with
      | zero => simpa using ha45
      | succ i => simpa using hlt i (by simp only [Fin.val_succ] at hi; omega)
    · cases i using Fin.cases with
      | zero =>
        simp only [Fin.val_zero] at hi
        omega
      | succ i => simpa using heq i (by simp only [Fin.val_succ] at hi; omega)

private lemma mem_holdWords_one (c : Fin 1 → ℤ) :
    c ∈ holdWords 1 (∑ i, c i) ↔ 2 ≤ c 0 ∧ c 0 ∈ ({4, 5} : Set ℤ) := by
  simp [mem_holdWords, Fin.forall_fin_one]

private lemma holdWords_indicator_cons (y : ℝ) {m : ℕ} (a : ℤ) (c : Fin (m + 1) → ℤ) :
    (holdWords (m + 2) (∑ i, (Fin.cons a c : Fin (m + 2) → ℤ) i)).indicator
        (fun c ↦ ∏ i, letterWt y (c i)) (Fin.cons a c : Fin (m + 2) → ℤ) =
      (({4, 5} : Set ℤ)ᶜ).indicator (letterWt y) a *
        (holdWords (m + 1) (∑ i, c i)).indicator (fun c ↦ ∏ i, letterWt y (c i)) c := by
  by_cases h2 : 2 ≤ a
  · by_cases h45 : a ∈ ({4, 5} : Set ℤ)
    · rw [Set.indicator_of_notMem (fun h ↦ ((mem_holdWords_cons a c).1 h).1.2 h45),
        Set.indicator_of_notMem (s := ({4, 5} : Set ℤ)ᶜ) (fun h ↦ h h45), zero_mul]
    · rw [Set.indicator_of_mem (s := ({4, 5} : Set ℤ)ᶜ) h45]
      by_cases hc : c ∈ holdWords (m + 1) (∑ i, c i)
      · rw [Set.indicator_of_mem ((mem_holdWords_cons a c).2 ⟨⟨h2, h45⟩, hc⟩),
          Set.indicator_of_mem hc, Fin.prod_univ_succ]
        simp
      · rw [Set.indicator_of_notMem (fun h ↦ hc ((mem_holdWords_cons a c).1 h).2),
          Set.indicator_of_notMem hc, mul_zero]
  · rw [Set.indicator_of_notMem (fun h ↦ h2 ((mem_holdWords_cons a c).1 h).1.1)]
    simp [Set.indicator_apply, letterWt_of_lt_two h2]

/-- The weight of a non-closing letter. -/
private noncomputable def sigmaNc (y : ℝ) : ℝ≥0∞ :=
  ∑' b : ℤ, (({4, 5} : Set ℤ)ᶜ).indicator (letterWt y) b

/-- The weight of a closing letter. -/
private noncomputable def sigmaCl (y : ℝ) : ℝ≥0∞ :=
  ∑' b : ℤ, ({4, 5} : Set ℤ).indicator (letterWt y) b

private lemma sum_words_eq (y : ℝ) (m : ℕ) :
    ∑' c : Fin (m + 1) → ℤ,
        (holdWords (m + 1) (∑ i, c i)).indicator (fun c ↦ ∏ i, letterWt y (c i)) c =
      sigmaNc y ^ m * sigmaCl y := by
  induction m with
  | zero =>
    rw [pow_zero, one_mul, sigmaCl, ← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
    refine tsum_congr fun b ↦ ?_
    by_cases h2 : 2 ≤ b
    · by_cases h45 : b ∈ ({4, 5} : Set ℤ)
      · rw [Set.indicator_of_mem ((mem_holdWords_one _).2 ⟨h2, h45⟩),
          Set.indicator_of_mem h45]
        simp
      · rw [Set.indicator_of_notMem (fun h ↦ h45 ((mem_holdWords_one _).1 h).2),
          Set.indicator_of_notMem h45]
    · rw [Set.indicator_of_notMem (fun h ↦ h2 ((mem_holdWords_one _).1 h).1)]
      simp [Set.indicator_apply, letterWt_of_lt_two h2]
  | succ m ih =>
    rw [← (Fin.consEquiv fun _ : Fin (m + 2) ↦ ℤ).tsum_eq]
    refine (tsum_congr fun p : ℤ × (Fin (m + 1) → ℤ) ↦
      holdWords_indicator_cons y p.1 p.2).trans ?_
    rw [ENNReal.tsum_prod (f := fun a c ↦ (({4, 5} : Set ℤ)ᶜ).indicator
      (letterWt y) a * (holdWords (m + 1) (∑ i, c i)).indicator (fun c ↦ ∏ i, letterWt y (c i)) c)]
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right, sigmaNc, pow_succ]
    ring

/-- The total letter weight `∑_b ϖ(b) y^b = y² / (2 - y)²` in `ℝ`. -/
private lemma hasSum_varpi_mul_zpow {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y < 2) :
    HasSum (fun b : ℤ ↦ varpi b * y ^ b) (y ^ 2 / (2 - y) ^ 2) := by
  have hinj : Function.Injective (fun n : ℕ ↦ (n : ℤ) + 2) := fun a b h ↦ by simpa using h
  rw [← hinj.hasSum_iff]
  swap
  · intro b hb
    have : b ≤ 1 := by
      by_contra h
      exact hb ⟨(b - 2).toNat, by simp only; omega⟩
    rw [varpi_of_le_one this, zero_mul]
  set x := y / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    rw [hx]
    linarith
  convert ((hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := x)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)).add
      (hasSum_geometric_of_lt_one hx0 hx1)).mul_left (x ^ 2) using 1
  · ext n
    simp only [Function.comp_apply, varpi_natCast_add_two]
    rw [show ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hx]
    ring
  · have h1x : (1 - x) ≠ 0 := by linarith
    have h2y : (2 - y) ≠ 0 := by linarith
    rw [hx] at h1x ⊢
    field_simp
    ring

/-- `ϖ(4) y⁴ + ϖ(5) y⁵ = (3/16) y⁴ + (1/8) y⁵`. -/
private lemma sigmaCl_eq {y : ℝ} (hy : 0 ≤ y) :
    sigmaCl y = ENNReal.ofReal (3 / 16 * y ^ 4 + 1 / 8 * y ^ 5) := by
  rw [sigmaCl, tsum_eq_sum (s := {4, 5}) fun b hb ↦ Set.indicator_of_notMem (by simpa using hb) _,
    Finset.sum_pair (by norm_num), Set.indicator_of_mem (by simp), Set.indicator_of_mem (by simp),
    letterWt, letterWt, varpi_four, varpi_five,
    ← ENNReal.ofReal_add (by norm_num; positivity) (by norm_num; positivity)]
  norm_num

private lemma sigmaNc_add_sigmaCl {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y < 2) :
    sigmaNc y + sigmaCl y = ENNReal.ofReal (y ^ 2 / (2 - y) ^ 2) := by
  have h := hasSum_varpi_mul_zpow hy0 hy2
  rw [sigmaNc, sigmaCl, ← ENNReal.tsum_add, ← h.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun b ↦ mul_nonneg (varpi_nonneg _) (zpow_nonneg hy0 _))
      h.summable]
  exact tsum_congr fun b ↦ congrFun (Set.indicator_compl_add_self _ _) b

/-- **Value of the vertical generating function.** For `0 < y < 2` with
`y² / (2 - y)² - (3/16) y⁴ - (1/8) y⁵ < 1`, the series `𝖵(y)` has the finite sum
`((3/16) y⁴ + (1/8) y⁵) / (1 - y² / (2 - y)² + (3/16) y⁴ + (1/8) y⁵)`. -/
@[collatz_pos_dens "lem_rn_hold_vpgf"]
theorem holdVpgf_eq {y : ℝ} (hy0 : 0 < y) (hy2 : y < 2)
    (h : y ^ 2 / (2 - y) ^ 2 - 3 / 16 * y ^ 4 - 1 / 8 * y ^ 5 < 1) :
    holdVpgf y = ENNReal.ofReal ((3 / 16 * y ^ 4 + 1 / 8 * y ^ 5) /
      (1 - y ^ 2 / (2 - y) ^ 2 + 3 / 16 * y ^ 4 + 1 / 8 * y ^ 5)) := by
  set A := y ^ 2 / (2 - y) ^ 2
  set C := 3 / 16 * y ^ 4 + 1 / 8 * y ^ 5 with hC
  have hC0 : 0 ≤ C := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hsum := sigmaNc_add_sigmaCl hy0.le hy2
  rw [sigmaCl_eq hy0.le] at hsum
  have hCA : C ≤ A := by
    rw [← ENNReal.ofReal_le_ofReal_iff hA0, ← hsum]
    exact le_add_self
  have hnc : sigmaNc y = ENNReal.ofReal (A - C) := by
    rw [ENNReal.ofReal_sub _ hC0]
    exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hsum
  have hD : 0 < 1 - A + C := by linarith
  rw [holdVpgf_eq_tsum_succ,
    ENNReal.tsum_prod (f := fun m l ↦ ENNReal.ofReal (holdLaw (m + 1) l * y ^ l))]
  simp_rw [sum_l_eq hy0, sum_words_eq, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, hnc,
    sigmaCl_eq hy0.le, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (sub_nonneg.2 hCA)]
  rw [show 1 - A + 3 / 16 * y ^ 4 + 1 / 8 * y ^ 5 = 1 - (A - C) by rw [hC]; ring,
    ENNReal.ofReal_div_of_pos (by linarith), ← hC, div_eq_mul_inv, mul_comm]

/-- Under the hypotheses of `holdVpgf_eq`, the series `𝖵(y)` is finite. -/
theorem holdVpgf_ne_top {y : ℝ} (hy0 : 0 < y) (hy2 : y < 2)
    (h : y ^ 2 / (2 - y) ^ 2 - 3 / 16 * y ^ 4 - 1 / 8 * y ^ 5 < 1) : holdVpgf y ≠ ∞ :=
  holdVpgf_eq hy0 hy2 h ▸ ENNReal.ofReal_ne_top

end CollatzPosDens
