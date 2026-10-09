/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The density constant `c_M`

This file defines the density constant
$$c_{\mathrm{M}} := \frac{1}{2^{33}\,\mathcal{M}\,m^{5633/2048}} \in \mathbb{R}_{>0},$$
where `𝓜` is the seed bound and `m` the fixed modulus exponent. It is the constant `c_M` such
that, for every sufficiently large real `X`, at least `c_M X` positive integers below `X` have
Collatz orbits reaching `1`.

## Main definitions

* `CollatzPosDens.densityConstOf`: the expression `1 / (2^33 M m^{5633/2048})` in
  parameters `M m : ℕ`.
* `CollatzPosDens.densityConst`: the density constant `c_M`, its value at `M = 𝓜`, `m = m`.

## Main results

* `CollatzPosDens.densityConst_def`: the defining formula of `c_M`.
* `CollatzPosDens.densityConst_pos`: `0 < c_M`.
* `CollatzPosDens.inv_densityConst`: `c_M⁻¹ = 2^33 𝓜 m^{5633/2048}`.
* `CollatzPosDens.two_pow_33_le_inv_densityConst`: `2^33 ≤ c_M⁻¹`.
* `CollatzPosDens.logb_inv_densityConst`:
  `log₂ c_M⁻¹ = 33 + log₂ 𝓜 + (5633/2048) log₂ m`.

## Implementation notes

The power `m^{5633/2048}` is Mathlib's real power `Real.rpow` of the natural number `m` cast to
`ℝ`, so `c_M` is real-valued. The constant is far too small to be evaluated, so `densityConst`
is irreducible and is used through `densityConst_def` and the lemmas of this file, which are
proved for the parametric expression `densityConstOf`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `1 / (2^33 M m^{5633/2048})` with parameters `M` and `m`; the density
constant `c_M` is `densityConstOf 𝓜 m`. -/
noncomputable def densityConstOf (M m : ℕ) : ℝ :=
  1 / (2 ^ 33 * (M : ℝ) * (m : ℝ) ^ (5633 / 2048 : ℝ))

/-- The defining formula of `densityConstOf`. -/
theorem densityConstOf_def (M m : ℕ) :
    densityConstOf M m = 1 / (2 ^ 33 * (M : ℝ) * (m : ℝ) ^ (5633 / 2048 : ℝ)) := rfl

/-- The inverse of `densityConstOf M m` is `2^33 M m^{5633/2048}`. -/
theorem inv_densityConstOf (M m : ℕ) :
    (densityConstOf M m)⁻¹ = 2 ^ 33 * (M : ℝ) * (m : ℝ) ^ (5633 / 2048 : ℝ) := by
  rw [densityConstOf_def, one_div, inv_inv]

/-- `densityConstOf M m` is positive when `M` and `m` are. -/
theorem densityConstOf_pos {M m : ℕ} (hM : 0 < M) (hm : 0 < m) : 0 < densityConstOf M m := by
  rw [densityConstOf_def]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hm' : (0 : ℝ) < (m : ℝ) ^ (5633 / 2048 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  positivity

/-- `2^33 ≤ (densityConstOf M m)⁻¹` when `1 ≤ M` and `1 ≤ m`. -/
theorem two_pow_33_le_inv_densityConstOf {M m : ℕ} (hM : 1 ≤ M) (hm : 1 ≤ m) :
    (2 : ℝ) ^ 33 ≤ (densityConstOf M m)⁻¹ := by
  rw [inv_densityConstOf]
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hm' : (1 : ℝ) ≤ (m : ℝ) ^ (5633 / 2048 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  calc (2 : ℝ) ^ 33 = 2 ^ 33 * 1 * 1 := by ring
    _ ≤ 2 ^ 33 * (M : ℝ) * (m : ℝ) ^ (5633 / 2048 : ℝ) := by gcongr

/-- `log₂ (densityConstOf M m)⁻¹ = 33 + log₂ M + (5633/2048) log₂ m` when `M` and `m` are
positive. -/
theorem logb_inv_densityConstOf {M m : ℕ} (hM : 0 < M) (hm : 0 < m) :
    Real.logb 2 (densityConstOf M m)⁻¹ =
      33 + Real.logb 2 M + (5633 / 2048 : ℝ) * Real.logb 2 m := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [inv_densityConstOf, Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hm' _).ne',
    Real.logb_mul (by positivity) hM'.ne', Real.logb_rpow_eq_mul_logb_of_pos hm']
  simp [Real.logb_pow]

/-- The density constant `c_M := 1 / (2^33 𝓜 m^{5633/2048}) ∈ ℝ_{>0}`, where `𝓜` is the seed
bound `seedBound` and `m` the modulus exponent `modulusExponent`. -/
@[collatz_pos_dens "def_cM", irreducible]
noncomputable def densityConst : ℝ := densityConstOf seedBound modulusExponent

/-- `c_M` is `densityConstOf` at `M = 𝓜` and `m = m`. -/
theorem densityConst_eq_densityConstOf :
    densityConst = densityConstOf seedBound modulusExponent := by
  unfold densityConst
  rfl

/-- The defining formula `c_M = 1 / (2^33 𝓜 m^{5633/2048})`. -/
theorem densityConst_def :
    densityConst =
      1 / (2 ^ 33 * (seedBound : ℝ) * (modulusExponent : ℝ) ^ (5633 / 2048 : ℝ)) :=
  densityConst_eq_densityConstOf.trans (densityConstOf_def _ _)

/-- The density constant is positive: `c_M ∈ ℝ_{>0}`. -/
@[collatz_pos_dens "def_cM"]
theorem densityConst_pos : 0 < densityConst :=
  densityConst_eq_densityConstOf ▸ densityConstOf_pos seedBound_pos modulusExponent_pos

/-- `c_M⁻¹ = 2^33 𝓜 m^{5633/2048}`. -/
theorem inv_densityConst :
    densityConst⁻¹ =
      2 ^ 33 * (seedBound : ℝ) * (modulusExponent : ℝ) ^ (5633 / 2048 : ℝ) :=
  densityConst_eq_densityConstOf ▸ inv_densityConstOf _ _

/-- `2^33 ≤ c_M⁻¹`. -/
theorem two_pow_33_le_inv_densityConst : (2 : ℝ) ^ 33 ≤ densityConst⁻¹ :=
  densityConst_eq_densityConstOf ▸
    two_pow_33_le_inv_densityConstOf seedBound_pos one_le_modulusExponent

/-- `log₂ c_M⁻¹ = 33 + log₂ 𝓜 + (5633/2048) log₂ m`. -/
theorem logb_inv_densityConst :
    Real.logb 2 densityConst⁻¹ =
      33 + Real.logb 2 seedBound + (5633 / 2048 : ℝ) * Real.logb 2 modulusExponent :=
  densityConst_eq_densityConstOf ▸ logb_inv_densityConstOf seedBound_pos modulusExponent_pos

end CollatzPosDens
