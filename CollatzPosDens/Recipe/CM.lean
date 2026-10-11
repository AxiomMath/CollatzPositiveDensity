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
# The construction's density constant `c_M(s)`

For an endpoint parameter `s ≥ 1`, this file defines the density constant of the construction,
$$c_{\mathrm{M}}(s) := \frac{1}{2^{33}\,\mathcal{M}(s)\,m(s)^{5633/2048}} \in \mathbb{R}_{>0},$$
where `𝓜(s)` is the seed allowance and `m(s)` the fixed modulus exponent. The construction
exhibits at least `c_M(s) X` odd integers below every real `X` beyond its cutoff that reach `s`
within both clocks.

## Main definitions

* `CollatzPosDens.densityConstOf`: the expression `1 / (2^33 M m^{5633/2048})` in
  parameters `M m : ℕ`.
* `CollatzPosDens.densityConst`: the density constant `c_M(s)`, its value at `M = 𝓜(s)`,
  `m = m(s)`.

## Main results

* `CollatzPosDens.densityConst_def`: the defining formula of `c_M(s)`.
* `CollatzPosDens.densityConst_pos`: `0 < c_M(s)` for `0 < s`.
* `CollatzPosDens.inv_densityConst`: `c_M(s)⁻¹ = 2^33 𝓜(s) m(s)^{5633/2048}`.
* `CollatzPosDens.two_pow_33_le_inv_densityConst`: `2^33 ≤ c_M(s)⁻¹` for `0 < s`.
* `CollatzPosDens.logb_inv_densityConst`:
  `log₂ c_M(s)⁻¹ = 33 + log₂ 𝓜(s) + (5633/2048) log₂ m(s)`.

## Implementation notes

The power `m^{5633/2048}` is Mathlib's real power `Real.rpow` of the natural number `m` cast to
`ℝ`, so `c_M(s)` is real-valued. The constant is far too small to be evaluated, so
`densityConst` is irreducible and is meant to be used through `densityConst_def` and the lemmas
of this file, which are proved for the parametric expression `densityConstOf`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `1 / (2^33 M m^{5633/2048})` with parameters `M` and `m`; the density
constant `c_M(s)` is `densityConstOf 𝓜(s) m(s)`. -/
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

/-- **The construction's density constant** `c_M(s) := 1 / (2^33 𝓜(s) m(s)^{5633/2048})`, where
`𝓜(s)` is the seed allowance and `m(s)` the fixed modulus exponent; it lies in `ℝ_{>0}` for
`s ≥ 1`. It is irreducible so that tactics never try to evaluate it; use `densityConst_def`. -/
@[collatz_pos_dens "def_cM", irreducible]
noncomputable def densityConst (s : ℕ) : ℝ := densityConstOf (seedBound s) (modulusExponent s)

/-- `c_M(s)` is `densityConstOf` at `M = 𝓜(s)` and `m = m(s)`. -/
theorem densityConst_eq_densityConstOf (s : ℕ) :
    densityConst s = densityConstOf (seedBound s) (modulusExponent s) := by
  unfold densityConst
  rfl

/-- The defining formula `c_M(s) = 1 / (2^33 𝓜(s) m(s)^{5633/2048})`. -/
theorem densityConst_def (s : ℕ) :
    densityConst s =
      1 / (2 ^ 33 * (seedBound s : ℝ) * (modulusExponent s : ℝ) ^ (5633 / 2048 : ℝ)) :=
  (densityConst_eq_densityConstOf s).trans (densityConstOf_def _ _)

/-- The density constant is positive: `c_M(s) ∈ ℝ_{>0}` for `0 < s`. -/
@[collatz_pos_dens "def_cM"]
theorem densityConst_pos {s : ℕ} (hs : 0 < s) : 0 < densityConst s :=
  (densityConst_eq_densityConstOf s) ▸
    densityConstOf_pos (seedBound_pos hs) (modulusExponent_pos s)

/-- `c_M(s)⁻¹ = 2^33 𝓜(s) m(s)^{5633/2048}`. -/
theorem inv_densityConst (s : ℕ) :
    (densityConst s)⁻¹ =
      2 ^ 33 * (seedBound s : ℝ) * (modulusExponent s : ℝ) ^ (5633 / 2048 : ℝ) :=
  (densityConst_eq_densityConstOf s) ▸ inv_densityConstOf _ _

/-- `2^33 ≤ c_M(s)⁻¹` for `0 < s`. -/
theorem two_pow_33_le_inv_densityConst {s : ℕ} (hs : 0 < s) :
    (2 : ℝ) ^ 33 ≤ (densityConst s)⁻¹ :=
  (densityConst_eq_densityConstOf s) ▸
    two_pow_33_le_inv_densityConstOf (seedBound_pos hs) (one_le_modulusExponent s)

/-- `log₂ c_M(s)⁻¹ = 33 + log₂ 𝓜(s) + (5633/2048) log₂ m(s)` for `0 < s`. -/
theorem logb_inv_densityConst {s : ℕ} (hs : 0 < s) :
    Real.logb 2 (densityConst s)⁻¹ =
      33 + Real.logb 2 (seedBound s) + (5633 / 2048 : ℝ) * Real.logb 2 (modulusExponent s) :=
  (densityConst_eq_densityConstOf s) ▸
    logb_inv_densityConstOf (seedBound_pos hs) (modulusExponent_pos s)

end CollatzPosDens
