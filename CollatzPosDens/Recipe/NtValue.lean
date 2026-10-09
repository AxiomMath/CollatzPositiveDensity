/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.F
public import CollatzPosDens.Recipe.Nt
public import CollatzPosDens.Recipe.PhBphys
public import CollatzPosDens.Recipe.PhDeltaEnclosure
public import CollatzPosDens.Recipe.PhLog23Enclosure
public import CollatzPosDens.Transfer.Log2C

/-!
# The value of the terminal threshold `N_t`

The terminal threshold is `N_t = ⌈X⌉` with
$$X := \frac{8\,(B_{\mathrm{ph}} + 121)}{5\delta}
  = \frac{8\,(23 + 121 + \log_2 3 + \log_2 (C + 1))}{5\delta}.$$
Inserting the lower bounds of `log₂ 3` and of `log₂ (C + 1)` together with the upper bound of
`δ` gives a rational lower bound for `X`, and the upper bounds of `log₂ 3` and `log₂ (C + 1)`
with the lower bound of `δ` give a rational upper bound. Both lie strictly between `9772293`
and `9772294` (they agree to `9772293.71943`), so `N_t = 9772294`.

## Main results

* `CollatzPosDens.terminalThreshold_eq`: `N_t = 9772294`.
* `CollatzPosDens.terminalThreshold_arg_mem_Ioo`: `9772293 < X < 9772294`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The argument `X = 8 (B_ph + 121) / (5δ)` of the ceiling defining `N_t` satisfies
`9772293 < X < 9772294`. -/
theorem terminalThreshold_arg_mem_Ioo :
    8 * (physicalExponent + 121) / (5 * logGrowthRate) ∈ Set.Ioo (9772293 : ℝ) 9772294 := by
  obtain ⟨a1, a2⟩ := logb_two_three_mem_Ioo
  obtain ⟨b1, b2, b3⟩ := logb_two_mixingConst_mem
  obtain ⟨d1, d2⟩ := logGrowthRate_mem_Ioo
  have hd : 0 < 5 * logGrowthRate := by linarith
  rw [physicalExponent_eq]
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

/-- **Value of the terminal threshold.** `N_t = 9772294`. -/
@[collatz_pos_dens "lem_Nt_value"]
theorem terminalThreshold_eq : terminalThreshold = 9772294 := by
  obtain ⟨h1, h2⟩ := terminalThreshold_arg_mem_Ioo
  rw [terminalThreshold_def, Nat.ceil_eq_iff (by norm_num)]
  constructor
  · norm_num; exact h1
  · exact_mod_cast h2.le

end CollatzPosDens
