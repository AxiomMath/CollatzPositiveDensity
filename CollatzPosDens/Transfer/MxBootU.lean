/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxChainRatio
public import CollatzPosDens.Transfer.S02Amix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logarithmic coefficient of the chained profile

Write `c_bt` for the ratio `CollatzPosDens.bootChainRatio` of the bootstrap chaining and
`a_mx(ι)` for the profile exponent `CollatzPosDens.amix` at the Fourier index `ι`. The exact
chained profile of the index `ι` carries the term `u_ι x^{-a_mx(ι)} log x`, whose coefficient is
the real constant `u_ι := 1 / (c_bt ^ a_mx(ι) - 1)`, with the positive real power; `u_b` denotes
its value at the bootstrap index. Since `c_bt > 1` and `a_mx(ι) > 0`, the base
`z := c_bt ^ a_mx(ι)` exceeds `1`, so `u_ι > 0`.

## Main definitions

* `CollatzPosDens.bootU`: the coefficient `u_ι := 1 / (c_bt ^ a_mx(ι) - 1) : ℝ`.

## Main results

* `CollatzPosDens.one_lt_bootChainRatio_rpow_amix`: `1 < c_bt ^ a_mx(ι)`.
* `CollatzPosDens.bootU_pos`: `0 < u_ι`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The bootstrap chaining ratio raised to the profile exponent of a Fourier index exceeds `1`:
`1 < c_bt ^ a_mx(ι)` (positive real power). -/
theorem one_lt_bootChainRatio_rpow_amix (ι : FIndex) :
    1 < (bootChainRatio : ℝ) ^ (amix ι : ℝ) := by
  apply Real.one_lt_rpow
  · exact_mod_cast one_lt_bootChainRatio
  · exact_mod_cast amix_pos ι

/-- The bootstrap chaining ratio raised to the profile exponent of the bootstrap index exceeds
`1`: `1 < c_bt ^ a_mx(b)` (positive real power). -/
theorem one_lt_bootChainRatio_rpow_amix_b :
    1 < (bootChainRatio : ℝ) ^ (amix .b : ℝ) :=
  one_lt_bootChainRatio_rpow_amix .b

/-- The logarithmic coefficient of the chained profile,
`u_ι := 1 / (c_bt ^ a_mx(ι) - 1) ∈ ℝ`, with the positive real power. -/
@[collatz_pos_dens "def_mx_boot_u"]
noncomputable def bootU (ι : FIndex) : ℝ := 1 / ((bootChainRatio : ℝ) ^ (amix ι : ℝ) - 1)

/-- The defining formula of the logarithmic coefficient of the chained profile. -/
theorem bootU_eq (ι : FIndex) : bootU ι = 1 / ((bootChainRatio : ℝ) ^ (amix ι : ℝ) - 1) := rfl

/-- The logarithmic coefficient of the chained profile is positive. -/
theorem bootU_pos (ι : FIndex) : 0 < bootU ι := by
  rw [bootU_eq]
  have := one_lt_bootChainRatio_rpow_amix ι
  exact one_div_pos.mpr (by linarith)

end CollatzPosDens
