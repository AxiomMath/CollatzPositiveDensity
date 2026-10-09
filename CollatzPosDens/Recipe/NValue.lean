/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.F
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhBphys
public import CollatzPosDens.Recipe.PhDeltaEnclosure
public import CollatzPosDens.Recipe.PhLog23Enclosure
public import CollatzPosDens.Transfer.Log2C
public import CollatzPosDens.Recipe.QstarGe

/-!
# The value of the generation threshold `N_*`

The generation threshold `N_* = ⌈8 (B_ph + 535/8) / (5δ)⌉` equals `9766262`.

Indeed `B_ph + 535/8 = 23 + 535/8 + log₂ 3 + log₂ (C + 1)`. The enclosures of `log₂ 3`,
`log₂ C < log₂ (C + 1)` and `δ` place the quantity `X = 8 (B_ph + 535/8) / (5δ)` between two
explicit rationals, both strictly between `9766261` and `9766262` (`X ≈ 9766261.1013516`), so
`⌈X⌉ = 9766262`.

## Main results

* `CollatzPosDens.generationThreshold_eq`: `N_* = 9766262`.
* `CollatzPosDens.le_conductor`: `9 N_* = 87896358 ≤ q_*`.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The value of `N_*`.** `N_* = 9766262`. -/
@[collatz_pos_dens "lem_N_value"]
theorem generationThreshold_eq : generationThreshold = 9766262 := by
  obtain ⟨a1, a2⟩ := logb_two_three_mem_Ioo
  obtain ⟨c1, c2, c3⟩ := logb_two_mixingConst_mem
  obtain ⟨d1, d2⟩ := logGrowthRate_mem_Ioo
  have hd : 0 < 5 * logGrowthRate := by linarith
  rw [generationThreshold_def, physicalExponent_eq, Nat.ceil_eq_iff (by norm_num)]
  push_cast
  constructor
  · rw [lt_div_iff₀ hd]
    nlinarith
  · rw [div_le_iff₀ hd]
    nlinarith

/-- The conductor is at least `9 N_* = 87896358`. -/
theorem le_conductor : 87896358 ≤ conductor := by
  have := nine_mul_generationThreshold_le_conductor
  rw [generationThreshold_eq] at this
  omega

end CollatzPosDens
