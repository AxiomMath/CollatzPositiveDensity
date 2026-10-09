/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxSubdensity
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Mixing.MxCoverDeficit
public import CollatzPosDens.Mixing.MxSubmassLe

/-!
# Mean deficit of the gate subdensity

Write `G_n = ResidueGroup n`, `ρ_n = refDensity n`, `g_n = mxSubdensity n`, `μ_n = refLaw n`,
`𝒰_n = mxGateUnion n`, `Sub^n_{𝒰_n} = subMass n (mxGateUnion n)`, and `⟨·⟩_n = residueAvg n`.
For every integer `n ≥ 2^{131072}`, the gate subdensity `g_n` is close to the reference density
`ρ_n` on average over `G_n`:
$$\langle \rho_n - g_n \rangle_n \le \frac{2}{3\, n^{9/8}}.$$

Pointwise, `ρ_n(y) - g_n(y) = (2/3) 3^n (μ_n(y) - Sub^n_{𝒰_n}(y))`, all values being finite since
`0 ≤ Sub^n_{𝒰_n}(y) ≤ μ_n(y) ≤ 1`. Averaging over `G_n` cancels the factor `3^n`, so the mean
deficit is `(2/3) ∑_y (μ_n(y) - Sub^n_{𝒰_n}(y))`, which is at most `(2/3) n^{-9/8}` by
`CollatzPosDens.sum_abs_refLaw_sub_subMass_mxGateUnion_le`.

## Main results

* `CollatzPosDens.residueAvg_refDensity_sub_mxSubdensity_le`: the bound above.
* `CollatzPosDens.refDensity_sub_mxSubdensity_eq`: the pointwise identity
  `ρ_n(y) - g_n(y) = (2/3) 3^n (μ_n(y) - Sub^n_{𝒰_n}(y))`.

## Implementation notes

The power `n^{9/8}` is the real power `(n : ℝ) ^ (9/8 : ℝ)`.

## References

* [Mazur, *Collatz positive density*], §13.10.
-/

@[expose] public section

namespace CollatzPosDens

/-- Pointwise, `ρ_n(y) - g_n(y) = (2/3) 3^n (μ_n(y)^ℝ - Sub^n_{𝒰_n}(y)^ℝ)`. -/
theorem refDensity_sub_mxSubdensity_eq (n : ℕ) (y : ResidueGroup n) :
    refDensity n y - mxSubdensity n y =
      2 / 3 * 3 ^ n * ((refLaw n y).toReal - (subMass n (mxGateUnion n) y).toReal) := by
  rw [refDensity, mxSubdensity_def]
  ring

/-- **Mean deficit of the subdensity.** For every integer `n ≥ 2^{131072}`,
`⟨ρ_n - g_n⟩_n ≤ 2 / (3 n^{9/8})`. -/
@[collatz_pos_dens "lem_mx_subdensity_deficit"]
theorem residueAvg_refDensity_sub_mxSubdensity_le (n : ℕ) (hn : 2 ^ 131072 ≤ n) :
    residueAvg n (fun y => refDensity n y - mxSubdensity n y) ≤
      2 / (3 * (n : ℝ) ^ (9 / 8 : ℝ)) := by
  have hcov := sum_abs_refLaw_sub_subMass_mxGateUnion_le n hn
  have hsum : ∑ y : ResidueGroup n,
      ((refLaw n y).toReal - (subMass n (mxGateUnion n) y).toReal) ≤ (n : ℝ) ^ (-(9 / 8 : ℝ)) :=
    (Finset.sum_le_sum fun y _ => le_abs_self _).trans hcov
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le (by positivity) hn
    exact_mod_cast this
  rw [residueAvg_def]
  simp_rw [refDensity_sub_mxSubdensity_eq]
  rw [← Finset.mul_sum]
  rw [Real.rpow_neg hn0.le] at hsum
  set S := ∑ y : ResidueGroup n,
    ((refLaw n y).toReal - (subMass n (mxGateUnion n) y).toReal)
  calc ((3 : ℝ) ^ n)⁻¹ * (2 / 3 * 3 ^ n * S) = 2 / 3 * S := by field_simp
    _ ≤ 2 / 3 * ((n : ℝ) ^ (9 / 8 : ℝ))⁻¹ := by gcongr
    _ = 2 / (3 * (n : ℝ) ^ (9 / 8 : ℝ)) := by field_simp

end CollatzPosDens
