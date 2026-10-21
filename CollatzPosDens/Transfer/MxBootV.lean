/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxBootU
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The constant coefficient of the chained profile

Write `c_bt` for the ratio `CollatzPosDens.bootChainRatio` of the bootstrap chaining and
`a_mx(ι)` for the profile exponent `CollatzPosDens.amix` at the Fourier index `ι`. The exact
chained profile of the index `ι` carries the term `v_ι x^{-a_mx(ι)}`, whose coefficient is the
real constant `v_ι := c_bt ^ a_mx(ι) · log c_bt / (c_bt ^ a_mx(ι) - 1) ^ 2`, with the positive
real power and the natural logarithm. Since `c_bt > 1` and `c_bt ^ a_mx(ι) > 1`, `v_ι > 0`.

## Main definitions

* `CollatzPosDens.bootV`: the coefficient
  `v_ι := c_bt ^ a_mx(ι) · log c_bt / (c_bt ^ a_mx(ι) - 1) ^ 2 : ℝ`.

## Main results

* `CollatzPosDens.bootV_eq_bootU`: `v_ι = c_bt ^ a_mx(ι) · log c_bt · u_ι ^ 2`, where `u_ι` is
  the logarithmic coefficient `CollatzPosDens.bootU ι`.
* `CollatzPosDens.bootV_pos`: `0 < v_ι`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The constant coefficient of the chained profile,
`v_ι := c_bt ^ a_mx(ι) · log c_bt / (c_bt ^ a_mx(ι) - 1) ^ 2 ∈ ℝ`, with the positive real power
and the natural logarithm. -/
@[collatz_pos_dens "def_mx_boot_v"]
noncomputable def bootV (ι : FIndex) : ℝ :=
  (bootChainRatio : ℝ) ^ (amix ι : ℝ) * Real.log bootChainRatio /
    ((bootChainRatio : ℝ) ^ (amix ι : ℝ) - 1) ^ 2

/-- The defining formula of the constant coefficient of the chained profile. -/
theorem bootV_eq (ι : FIndex) :
    bootV ι = (bootChainRatio : ℝ) ^ (amix ι : ℝ) * Real.log bootChainRatio /
      ((bootChainRatio : ℝ) ^ (amix ι : ℝ) - 1) ^ 2 := rfl

/-- The constant coefficient of the chained profile in terms of the logarithmic coefficient:
`v_ι = c_bt ^ a_mx(ι) · log c_bt · u_ι ^ 2`. -/
theorem bootV_eq_bootU (ι : FIndex) :
    bootV ι = (bootChainRatio : ℝ) ^ (amix ι : ℝ) * Real.log bootChainRatio * bootU ι ^ 2 := by
  rw [bootV_eq, bootU_eq, div_pow, one_pow, mul_one_div]

/-- The logarithm of the bootstrap chaining ratio is positive. -/
theorem log_bootChainRatio_pos : 0 < Real.log (bootChainRatio : ℝ) :=
  Real.log_pos (by exact_mod_cast one_lt_bootChainRatio)

/-- The constant coefficient of the chained profile is positive. -/
theorem bootV_pos (ι : FIndex) : 0 < bootV ι := by
  have hz := one_lt_bootChainRatio_rpow_amix ι
  rw [bootV_eq]
  have : 0 < ((bootChainRatio : ℝ) ^ (amix ι : ℝ) - 1) ^ 2 := by
    have : 0 < (bootChainRatio : ℝ) ^ (amix ι : ℝ) - 1 := by linarith
    positivity
  exact div_pos (mul_pos (by linarith) log_bootChainRatio_pos) this

end CollatzPosDens
