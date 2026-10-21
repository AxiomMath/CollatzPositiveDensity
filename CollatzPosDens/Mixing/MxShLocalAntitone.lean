/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxShLocal
public import CollatzPosDens.Mixing.MxShLogLower
public import CollatzPosDens.Mixing.MxShLogPowerAntitone

/-!
# The local profile of the shell cut is antitone

For every Fourier index `ι` and all reals `n₀ ≤ x ≤ y`, where `n₀ = 2^80` is the mixing gate
level `CollatzPosDens.mxGateLevel`, the local profile `Q_ι` (`CollatzPosDens.mxShLocal`)
satisfies `Q_ι(y) ≤ Q_ι(x)`.

Indeed `log x ≥ 160/3` and `a_mx(ι) ≥ 1`, so `a_mx(ι) log x ≥ 1` and the damped logarithm
`t ↦ t ^ (-a_mx(ι)) log t` is antitone on `[x, ∞)`; the term `t ↦ t ^ (-2)` is antitone on
`(0, ∞)`, and `B_F(ι) ≥ 0`.

## Main results

* `CollatzPosDens.mxShLocal_antitone`: `Q_ι(y) ≤ Q_ι(x)` for `n₀ ≤ x ≤ y`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The local profile of the shell cut is antitone beyond the mixing gate level: for every
Fourier index `ι` and reals `n₀ ≤ x ≤ y`, `Q_ι(y) ≤ Q_ι(x)`. -/
@[collatz_pos_dens "lem_mx_sh_local_antitone"]
theorem mxShLocal_antitone (ι : FIndex) {x y : ℝ} (hx : (mxGateLevel : ℝ) ≤ x) (hxy : x ≤ y) :
    mxShLocal ι y ≤ mxShLocal ι x := by
  have hlog := le_log_of_two_pow_eighty_le hx
  have hx1 : 1 < x := by
    have : (1 : ℝ) < mxGateLevel := by
      rw [mxGateLevel_def]; norm_num
    linarith
  have hx0 : 0 < x := by linarith
  have ha : (1 : ℝ) ≤ amix ι := by exact_mod_cast (one_lt_amix ι).le
  have hal : 1 ≤ (amix ι : ℝ) * Real.log x := by nlinarith
  have hmain := rpow_neg_mul_log_le_of_one_le_mul_log hx1 hxy hal
  have hsq : y ^ (-2 : ℝ) ≤ x ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hx0 hxy (by norm_num)
  have hB := fourierPrefactor_nonneg ι
  rw [mxShLocal_def, mxShLocal_def]
  have h1 : 18 * fourierPrefactor ι * (y ^ (-(amix ι : ℝ)) * Real.log y) ≤
      18 * fourierPrefactor ι * (x ^ (-(amix ι : ℝ)) * Real.log x) := by gcongr
  linarith [h1]

end CollatzPosDens
