/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxShLocal
public import CollatzPosDens.Transfer.MxExactProfile

/-!
# The shift identity of the exact chained profile

Write `c = c_bt = 1079/1000` for the ratio `CollatzPosDens.bootChainRatio` of the chaining,
`𝔐^ex_ι` for the exact chained profile `CollatzPosDens.mxExactProfile ι` and `Q_ι` for the local
profile `CollatzPosDens.mxShLocal ι` of the shell cut. For every Fourier index `ι` and every real
`x > 0`,
$$\mathfrak M^{\mathrm{ex}}_\iota(c x) + Q_\iota(c x) = \mathfrak M^{\mathrm{ex}}_\iota(x).$$

With `a = a_mx(ι) > 0` and `z = c ^ a > 1`, one has `(c x) ^ (-a) = z⁻¹ x ^ (-a)`,
`(c x) ^ (-2) = c⁻² x ^ (-2)` and `log (c x) = log c + log x`; the coefficients
`u_ι = 1/(z-1)`, `v_ι = z log c/(z-1)^2` and `w_b = 15/(c^2-1)` are exactly those making
`z⁻¹ (u_ι + 1) = u_ι`, `z⁻¹ ((u_ι + 1) log c + v_ι) = v_ι` and `c⁻² (w_b + 15) = w_b`.

## Main results

* `CollatzPosDens.mxExactProfile_shift`: `𝔐^ex_ι(c x) + Q_ι(c x) = 𝔐^ex_ι(x)` for `0 < x`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The shift identity of the exact chained profile: for every Fourier index `ι` and every real
`x > 0`, `𝔐^ex_ι(c_bt x) + Q_ι(c_bt x) = 𝔐^ex_ι(x)`, where `c_bt` is the ratio of the chaining,
`𝔐^ex_ι` the exact chained profile and `Q_ι` the local profile of the shell cut. -/
@[collatz_pos_dens "lem_mx_boot_shift"]
theorem mxExactProfile_shift (ι : FIndex) {x : ℝ} (hx : 0 < x) :
    mxExactProfile ι ((bootChainRatio : ℝ) * x) + mxShLocal ι ((bootChainRatio : ℝ) * x) =
      mxExactProfile ι x := by
  have hc1 : (1 : ℝ) < bootChainRatio := by exact_mod_cast one_lt_bootChainRatio
  have hc0 : (0 : ℝ) < bootChainRatio := by linarith
  have hz := one_lt_bootChainRatio_rpow_amix ι
  have hW : (bootW : ℝ) = 15 / ((bootChainRatio : ℝ) ^ 2 - 1) := by
    rw [bootW_eq]; push_cast; rfl
  have hc2 : (bootChainRatio : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [mxExactProfile_eq, mxExactProfile_eq, mxShLocal_def, Real.mul_rpow hc0.le hx.le,
    Real.mul_rpow hc0.le hx.le, Real.log_mul hc0.ne' hx.ne', Real.rpow_neg hc0.le,
    Real.rpow_neg hc0.le, Real.rpow_two, bootU_eq, bootV_eq, hW]
  set z := (bootChainRatio : ℝ) ^ (amix ι : ℝ) with hzdef
  set c := (bootChainRatio : ℝ)
  have hz1 : z - 1 ≠ 0 := by linarith
  have hz0 : z ≠ 0 := by linarith
  field_simp
  ring

end CollatzPosDens
