/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.FirstCrossing.FcLowerTail

/-!
# Lower tail of valuation sums with an exact tilt

Under the geometric mass `𝐩`, the letters of a word `x ∈ ℤ_{≥1}^H` behave like independent
geometric variables of mean `2`. This file proves the lower-tail bound with an exact exponential
tilt: for integers `H, v ≥ 0` and a real `0 ≤ δ < 1`,
`𝐩({x ∈ ℤ_{≥1}^H : A(x) - 2H ≤ -v}) ≤ (1 - δ)^v (1 - δ²)^{-H}`.

With `z = 1 - δ`, the per-letter moment `∑_{a ≥ 1} 2^{-a} z^{a-2} = 1/(z(2 - z)) = (1 - δ²)⁻¹`
is evaluated exactly, by the geometric series. On the set in question `z^{A(x) - 2H + v} ≥ 1`,
so its mass is at most `z^v ∑_x 2^{-A(x)} z^{A(x) - 2H} = z^v (1 - δ²)^{-H}`.

## Main results

* `CollatzPosDens.fcTiltLower_geomMass_le`: the lower-tail bound with an exact tilt.

## Implementation notes

Words of length `H` stand for `ℤ_{≥1}^H`. The tilt `z^{A(x) - 2H}` is written
`exp (log z * (A(x) - 2H))`, so that the factorisation `fcLowerTail_tsum_tilt` applies with
`s = log z`. The right-hand side is the real number `(1 - δ)^v ((1 - δ²)^H)⁻¹` viewed in `ℝ≥0∞`.
The hypotheses `H ≥ 1` and `0 < δ` of [mazur2026] are not needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- **Lower tail with an exact tilt.** For natural numbers `H, v` and a real `0 ≤ δ < 1`,
`𝐩({x ∈ ℤ_{≥1}^H : A(x) - 2H ≤ -v}) ≤ (1 - δ)^v (1 - δ²)^{-H}`. -/
@[collatz_pos_dens "lem_fc_tilt_lower"]
theorem fcTiltLower_geomMass_le (H v : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    geomMass {x : Word | x.length = H ∧ (x.valSum : ℤ) - 2 * H ≤ -v} ≤
      ENNReal.ofReal ((1 - δ) ^ v * ((1 - δ ^ 2) ^ H)⁻¹) := by
  set z := 1 - δ with hz
  have hz0 : 0 < z := by linarith
  have hz1 : z ≤ 1 := by linarith
  set s := log z with hs
  have hes : exp s = z := exp_log hz0
  have hlog : s ≤ 0 := log_nonpos hz0.le hz1
  have hexp : exp s < 2 := by linarith
  set φ := ∑' a : ℕ, (1 / 2 : ℝ) ^ (a + 1) * exp (s * (((a + 1 : ℕ) : ℝ) - 2))
  have hφ : φ = (1 - δ ^ 2)⁻¹ := by
    rw [show φ = _ from (fcMgf_hasSum hexp).tsum_eq, exp_neg, hes]
    have h2 : (2 : ℝ) - z ≠ 0 := by linarith
    have h3 : (1 : ℝ) - δ ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  have hpt : ∀ x : {x : Word | x.length = H ∧ (x.valSum : ℤ) - 2 * H ≤ -v},
      (x : Word).massWeight ≤ ENNReal.ofReal (z ^ v) * fcLowerTailTilt s x := by
    rintro ⟨x, hxl, hxv⟩
    simp only [Word.massWeight, fcLowerTailTilt, hxl]
    have hxz : (x.valSum : ℤ) - 2 * H + v ≤ 0 := by omega
    have hxv' : ((x.valSum : ℝ) - 2 * H) + v ≤ 0 := by exact_mod_cast hxz
    rw [mul_left_comm, ← ENNReal.ofReal_mul (pow_nonneg hz0.le _), ← hes, ← exp_nat_mul,
      ← exp_add]
    exact le_mul_of_one_le_right' (ENNReal.one_le_ofReal.mpr (one_le_exp (by nlinarith)))
  calc geomMass {x : Word | x.length = H ∧ (x.valSum : ℤ) - 2 * H ≤ -v}
      ≤ ∑' x : {x : Word | x.length = H ∧ (x.valSum : ℤ) - 2 * H ≤ -v},
          ENNReal.ofReal (z ^ v) * fcLowerTailTilt s x :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (z ^ v) *
          ∑' x : {x : Word | x.length = H ∧ (x.valSum : ℤ) - 2 * H ≤ -v},
            fcLowerTailTilt s x := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (z ^ v) * ∑' x : {x : Word | x.length = H}, fcLowerTailTilt s x := by
        gcongr 1
        exact ENNReal.tsum_mono_subtype _ fun x hx => hx.1
    _ = ENNReal.ofReal (z ^ v) * ENNReal.ofReal φ ^ H := by
        rw [fcLowerTail_tsum_tilt hexp]
    _ = ENNReal.ofReal ((1 - δ) ^ v * ((1 - δ ^ 2) ^ H)⁻¹) := by
        have hφ0 : 0 ≤ φ := by rw [hφ]; exact inv_nonneg.mpr (by nlinarith)
        rw [← ENNReal.ofReal_pow hφ0, ← ENNReal.ofReal_mul (pow_nonneg hz0.le _), hφ, inv_pow]

end CollatzPosDens
