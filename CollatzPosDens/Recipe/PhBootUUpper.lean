/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhBootPowerLower
public import CollatzPosDens.Transfer.MxBootU

/-!
# An upper bound for `bootU .b`

The logarithmic coefficient of the bootstrap profile is `bootU .b = 1/(z - 1)` with
`z = bootChainRatio ^ amix .b`. Since `z > 1116557504/10^9`, we have `z - 1 > 116557504/10^9 > 0`,
and as `t ↦ 1/t` decreases on the positive reals,
$$0 < \mathtt{bootU}\ b < \frac{10^9}{116557504} = 8.57945619700298\ldots
  < \frac{857945620}{10^8}.$$

## Main results

* `CollatzPosDens.bootU_mem_Ioo`: `0 < bootU .b < 857945620/10^8`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The logarithmic coefficient `bootU .b = 1/(bootChainRatio ^ amix .b - 1)` of the bootstrap
profile satisfies `0 < bootU .b < 857945620/10^8`. -/
@[collatz_pos_dens "lem_ph_boot_u_upper"]
theorem bootU_mem_Ioo : 0 < bootU .b ∧ bootU .b < 857945620 / 10 ^ 8 := by
  have hz := lt_bootChainRatio_rpow_amix_b
  have hpos : (0 : ℝ) < (bootChainRatio : ℝ) ^ (amix .b : ℝ) - 1 := by linarith
  refine ⟨by rw [bootU_eq]; positivity, ?_⟩
  rw [bootU_eq, div_lt_iff₀ hpos]
  nlinarith

end CollatzPosDens
