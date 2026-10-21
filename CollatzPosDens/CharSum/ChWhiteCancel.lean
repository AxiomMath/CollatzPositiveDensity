/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSignedFrac
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.CharSum.ChCosQuartic
public import CollatzPosDens.CharSum.ChExpCubic
public import CollatzPosDens.CharSum.ChPacketFn
public import CollatzPosDens.CharSum.ChRaw3Numeric
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.CharSum.ChV0Lower
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.S02Kappa
public import CollatzPosDens.Transfer.S02Z

/-!
# Cancellation at a white point

Fix `n : ℕ` and `ξ ∈ G_n`. If the angle `ϑ = ϑ_{n,ξ}(p)` of a point `p` satisfies `|ϑ| > ε_*`,
then the raw factor with `c = 3` is small: `φ₃(p) < exp(-κ_* z_*)`.

With `φ = πϑ`, the raw factor is the packet function of length `2`, whose exponents `2^a - 1` are
`0, 1`; hence `φ₃(p) = ½ |1 + e^{2iφ}| = |e^{iφ} cos φ| = cos (π|ϑ|)`, since `|ϑ| ≤ ½`. The
rational angle `v∘` satisfies `0 < v∘ < π ε_* < π|ϑ| ≤ π / 2`, so
`cos (π|ϑ|) < cos v∘ ≤ 1 - v∘² / 2 + v∘⁴ / 24 < 1 - y + y² / 2 - y³ / 6 ≤ e^{-y}` with
`y = 423871 / 62500000 = κ_* z_*`.

## Main results

* `CollatzPosDens.chRawFactor_three_eq_cos`: `φ₃(p) = cos (π |ϑ_{n,ξ}(p)|)`.
* `CollatzPosDens.chPairFactor_three_lt_exp`: `φ₃(p) < exp(-κ_* z_*)` whenever
  `|ϑ_{n,ξ}(p)| > ε_*`.

## Implementation notes

The statement holds for every point `p : ℤ × ℤ`, not only for points of the lattice `𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The raw factor with `c = 3` is `cos (π |ϑ_{n,ξ}(p)|)`. -/
theorem chRawFactor_three_eq_cos (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) :
    chRawFactor n ξ 3 p = Real.cos (π * |bkTheta n ξ p|) := by
  rw [chRawFactor_of_two_le n ξ (by norm_num : (2 : ℤ) ≤ 3),
    show ((3 : ℤ) - 1).toNat = 2 by rfl, chPacketFn_def, Finset.sum_range_succ,
    Finset.sum_range_one]
  set θ := bkTheta n ξ p
  set φ := π * θ
  have hkey : Complex.exp (2 * π * I * (((2 : ℝ) ^ 0 - 1) * θ : ℝ)) +
      Complex.exp (2 * π * I * (((2 : ℝ) ^ 1 - 1) * θ : ℝ)) =
      Complex.exp (φ * I) * (2 * (Real.cos φ : ℂ)) := by
    have h1 : Complex.exp (φ * I) * Complex.exp (-(φ * I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have harg : 2 * π * I * (((2 : ℝ) ^ 1 - 1) * θ : ℝ) = φ * I + φ * I := by
      simp only [φ]
      push_cast
      ring
    rw [harg, ofReal_cos, Complex.cos, Complex.exp_add]
    norm_num
    linear_combination (-1 : ℂ) * h1
  have hn : ‖Complex.exp (φ * I)‖ = 1 := norm_exp_ofReal_mul_I φ
  have hθ : |θ| ≤ 1 / 2 := abs_bkTheta_le n ξ _
  have hcos : Real.cos φ = Real.cos (π * |θ|) := by
    rcases abs_cases θ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cos_neg]
  have hnn : 0 ≤ Real.cos (π * |θ|) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [pi_pos, abs_nonneg θ]
  rw [hkey, norm_mul, hn, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hcos,
    abs_of_nonneg hnn]
  norm_num
  ring

/-- **Cancellation at a white point.** If `|ϑ_{n,ξ}(p)| > ε_*`, then the raw factor satisfies
`φ₃(p) < exp(-κ_* z_*)`. -/
@[collatz_pos_dens "lem_ch_white_cancel"]
theorem chPairFactor_three_lt_exp {n : ℕ} {ξ : ResidueGroup n} {p : ℤ × ℤ}
    (h : (epsStar : ℝ) < |bkTheta n ξ p|) :
    chRawFactor n ξ 3 p < Real.exp (-((kappaStar : ℝ) * zStar)) := by
  rw [chRawFactor_three_eq_cos, kappaStar_cast, zStar_cast]
  set τ := |bkTheta n ξ p|
  have hτ : τ ≤ 1 / 2 := abs_bkTheta_le n ξ _
  obtain ⟨hv0, hv1⟩ := chV0_pos_lt
  have hlt : Real.cos (π * τ) < Real.cos (chV0 : ℝ) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hv0.le (by nlinarith [pi_pos])
      (by nlinarith [pi_pos])
  have hq := cos_le_one_sub_sq_div_two_add_pow_four_div (chV0 : ℝ)
  have hr := ch_raw3_numeric_real
  have he := cubic_le_exp_neg (t := 423871 / 62500000) (by norm_num)
  have hy : (3187 / 20000 : ℝ) * (133 / 3125) = 423871 / 62500000 := by norm_num
  rw [hy]
  linarith

end CollatzPosDens
