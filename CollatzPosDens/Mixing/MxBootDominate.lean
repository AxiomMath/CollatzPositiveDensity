/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxShLocal
public import CollatzPosDens.Transfer.MxExactProfile

/-!
# The exact chained profile dominates the local profile

For every Fourier index `ι` and every real `x ≥ 1`, the local profile `Q_ι` of the shell cut
(`CollatzPosDens.mxShLocal ι`) is at most the exact chained profile `𝔐^ex_ι`
(`CollatzPosDens.mxExactProfile ι`).

With `c = c_bt = 1079/1000`, `a = a_mx(ι)`, which is `18693/10000` or `29/20` and so lies in
`(0, 2]`, and `z = c ^ a`, one has `1 < z ≤ c ^ 2 < 2`, hence `u_ι = 1/(z-1) ≥ 1`, `v_ι ≥ 0` and
`w_b = 15/(c^2-1) ≥ 15`; then
$$\mathfrak M^{\mathrm{ex}}_\iota(x) - Q_\iota(x) = 18 B_{\mathrm F}(\iota)\, x^{-a}
  \bigl((u_\iota - 1)\log x + v_\iota\bigr) + (w_{\mathrm b} - 15) x^{-2} \ge 0.$$

## Main results

* `CollatzPosDens.mxShLocal_le_mxExactProfile`: `Q_ι(x) ≤ 𝔐^ex_ι(x)` for `1 ≤ x`.
* `CollatzPosDens.one_le_bootU`: `1 ≤ u_ι`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The logarithmic coefficient of the exact chained profile is at least `1`:
`1 ≤ u_ι = 1/(c_bt ^ a_mx(ι) - 1)`, since `1 < c_bt ^ a_mx(ι) ≤ c_bt ^ 2 < 2`. -/
theorem one_le_bootU (ι : FIndex) : 1 ≤ bootU ι := by
  have hc1 : (1 : ℝ) ≤ bootChainRatio := by exact_mod_cast one_lt_bootChainRatio.le
  have ha : (amix ι : ℝ) ≤ 2 := by exact_mod_cast (amix_lt_two ι).le
  have hz := one_lt_bootChainRatio_rpow_amix ι
  have hz2 : (bootChainRatio : ℝ) ^ (amix ι : ℝ) ≤ (bootChainRatio : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hc1 ha
  have hc2 : (bootChainRatio : ℝ) ^ (2 : ℝ) = 1164241 / 1000000 := by
    rw [Real.rpow_two, bootChainRatio_cast]; norm_num
  rw [bootU_eq, le_div_iff₀ (by linarith)]
  linarith

/-- The exact chained profile dominates the local profile: for every Fourier index `ι` and every
real `x ≥ 1`, `Q_ι(x) ≤ 𝔐^ex_ι(x)`, where `𝔐^ex_ι` is the exact chained profile and `Q_ι` the
local profile of the shell cut. -/
@[collatz_pos_dens "lem_mx_boot_dominate"]
theorem mxShLocal_le_mxExactProfile (ι : FIndex) {x : ℝ} (hx : 1 ≤ x) :
    mxShLocal ι x ≤ mxExactProfile ι x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog := Real.log_nonneg hx
  have hu := one_le_bootU ι
  have hv := bootV_pos ι
  have hw : (15 : ℝ) ≤ bootW := by rw [bootW_cast]; norm_num
  have hB := fourierPrefactor_nonneg ι
  have hp := (Real.rpow_pos_of_pos hx0 (-(amix ι : ℝ))).le
  have hq := (Real.rpow_pos_of_pos hx0 (-2 : ℝ)).le
  rw [mxShLocal_def, mxExactProfile_eq, ← sub_nonneg]
  have h1 : 0 ≤ 18 * fourierPrefactor ι * x ^ (-(amix ι : ℝ)) *
      ((bootU ι - 1) * Real.log x + bootV ι) := by
    have : 0 ≤ (bootU ι - 1) * Real.log x := mul_nonneg (by linarith) hlog
    have : 0 ≤ (bootU ι - 1) * Real.log x + bootV ι := by linarith
    positivity
  have h2 : 0 ≤ ((bootW : ℝ) - 15) * x ^ (-2 : ℝ) := mul_nonneg (by linarith) hq
  nlinarith [h1, h2]

end CollatzPosDens
