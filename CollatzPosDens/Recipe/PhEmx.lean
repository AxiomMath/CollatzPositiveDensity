/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Recipe.PhHhist
public import CollatzPosDens.Transfer.S02Amix
public import CollatzPosDens.Transfer.S02Bstar
public import CollatzPosDens.Transfer.MxBootV

/-!
# The mixing part `E_j^mx` of the propagation majorant

For an integer `j ≥ 1` the mixing part of the propagation majorant is the real number
$$\mathsf E^{\mathrm{mx}}_j := 36\,\mathcal H_{\mathrm{hist}}\,B_{\mathrm F}(\mathrm b)
  \,2^{-12a_{\mathrm{mx}}(\mathrm b)}\,j^{5/2}\,\mathsf g^{-(a_{\mathrm{mx}}(\mathrm b)-\frac12)j}
  \,\bigl(u_{\mathrm b}(12\log 2 + j\log\mathsf g)+v_{\mathrm b}\bigr),$$
where `𝓗_hist = 344` is the histogram constant, `B_F(b)` the Fourier prefactor at the
bootstrap index, `a_mx(b) = 29/20` the profile exponent at that index, `𝗀 = 101/100` the
physical growth ratio, `u_b`, `v_b` the coefficients of the bootstrap profile, all powers are
positive real powers and `log` is the natural logarithm. The logarithmic factor is evaluated at
the gate `2^12 𝗀^j`, whose logarithm is `12 log 2 + j log 𝗀`. It is the contribution of the
logarithmic term of the bootstrap mixing profile `𝔐_b` to the propagation majorant `E_j`.

## Main definitions

* `CollatzPosDens.propagationMixingMajorant`: the mixing part `E_j^mx`, as a function `ℕ → ℝ`.

## Main results

* `CollatzPosDens.propagationMixingMajorant_def`: the defining formula of `E_j^mx`.
* `CollatzPosDens.twelve_mul_log_two_add_mul_log_growthRatio`:
  `12 log 2 + j log 𝗀 = log (2^12 𝗀 ^ j)`.
* `CollatzPosDens.bootU_mul_log_add_bootV_pos`: `0 < u_b (12 log 2 + j log 𝗀) + v_b`.
* `CollatzPosDens.propagationMixingMajorant_nonneg`: `0 ≤ E_j^mx` for every `j`.
* `CollatzPosDens.propagationMixingMajorant_pos`: `0 < E_j^mx` for `1 ≤ j`.

## Implementation notes

The majorant is defined for every natural number `j`, through `Real.rpow`; at `j = 0` it
vanishes because of the factor `j ^ (5/2)`, and for `j ≥ 1` it is the quantity `E_j^mx` above.
The Fourier index is fixed at `b`, so the majorant takes no index argument.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The mixing part of the propagation majorant
`E_j^mx := 36 𝓗_hist B_F(b) 2 ^ (-12 a_mx(b)) j ^ (5/2) 𝗀 ^ (-(a_mx(b) - 1/2) j)
(u_b (12 log 2 + j log 𝗀) + v_b)`, with positive real powers and the natural logarithm. -/
@[collatz_pos_dens "def_ph_Emx"]
noncomputable def propagationMixingMajorant (j : ℕ) : ℝ :=
  36 * (Hhist : ℝ) * fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ))) *
    (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ (-(((amix .b : ℝ) - 1 / 2) * j)) *
    (bootU .b * (12 * Real.log 2 + j * Real.log (growthRatio : ℝ)) + bootV .b)

/-- The defining formula of the mixing part of the propagation majorant. -/
theorem propagationMixingMajorant_def (j : ℕ) :
    propagationMixingMajorant j =
      36 * (Hhist : ℝ) * fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ))) *
        (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ (-(((amix .b : ℝ) - 1 / 2) * j)) *
        (bootU .b * (12 * Real.log 2 + j * Real.log (growthRatio : ℝ)) + bootV .b) := rfl

/-- The logarithmic factor of `E_j^mx` is the logarithm of the gate `2 ^ 12 𝗀 ^ j`. -/
theorem twelve_mul_log_two_add_mul_log_growthRatio (j : ℕ) :
    12 * Real.log 2 + j * Real.log (growthRatio : ℝ) =
      Real.log (2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ)) := by
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos growthRatio_cast_pos _).ne',
    Real.log_rpow growthRatio_cast_pos, Real.log_pow]
  push_cast; ring

/-- The logarithm `12 log 2 + j log 𝗀` is positive. -/
theorem twelve_mul_log_two_add_mul_log_growthRatio_pos (j : ℕ) :
    0 < 12 * Real.log 2 + j * Real.log (growthRatio : ℝ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg : 0 < Real.log (growthRatio : ℝ) := Real.log_pos one_lt_growthRatio_cast
  have : 0 ≤ (j : ℝ) * Real.log (growthRatio : ℝ) := mul_nonneg (Nat.cast_nonneg j) hg.le
  linarith

/-- The affine logarithmic factor `u_b (12 log 2 + j log 𝗀) + v_b` of `E_j^mx` is positive. -/
theorem bootU_mul_log_add_bootV_pos (j : ℕ) :
    0 < bootU .b * (12 * Real.log 2 + j * Real.log (growthRatio : ℝ)) + bootV .b :=
  add_pos (mul_pos (bootU_pos .b) (twelve_mul_log_two_add_mul_log_growthRatio_pos j))
    (bootV_pos .b)

/-- The prefactor `36 𝓗_hist B_F(b) 2 ^ (-12 a_mx(b))` of `E_j^mx` is positive. -/
private lemma propagationMixingMajorant_prefactor_pos :
    0 < 36 * (Hhist : ℝ) * fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ))) := by
  have hH : (0 : ℝ) < Hhist := by exact_mod_cast Hhist_pos
  exact mul_pos (mul_pos (mul_pos (by norm_num) hH) (fourierPrefactor_pos .b))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- The mixing part of the propagation majorant is nonnegative. -/
theorem propagationMixingMajorant_nonneg (j : ℕ) : 0 ≤ propagationMixingMajorant j := by
  rw [propagationMixingMajorant_def]
  exact mul_nonneg (mul_nonneg (mul_nonneg propagationMixingMajorant_prefactor_pos.le
    (Real.rpow_nonneg (Nat.cast_nonneg j) _)) (Real.rpow_nonneg growthRatio_cast_pos.le _))
    (bootU_mul_log_add_bootV_pos j).le

/-- The mixing part of the propagation majorant is positive for `1 ≤ j`. -/
theorem propagationMixingMajorant_pos {j : ℕ} (hj : 1 ≤ j) :
    0 < propagationMixingMajorant j := by
  rw [propagationMixingMajorant_def]
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  exact mul_pos (mul_pos (mul_pos propagationMixingMajorant_prefactor_pos
    (Real.rpow_pos_of_pos hj' _)) (Real.rpow_pos_of_pos growthRatio_cast_pos _))
    (bootU_mul_log_add_bootV_pos j)

end CollatzPosDens
