/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.FirstCrossing.PhDelta
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.PhDeltaEnclosure

/-!
# The real endpoint `16 + N_* δ`

We prove `16 + N_* δ < 140214`, where `N_*` is the generation threshold `generationThreshold`
and `δ = log₂ (101/100)` is the logarithmic growth rate `logGrowthRate`.

Since `N_* = 9766262` and `δ < 0.014355292977070041432`, exact rational arithmetic gives
`16 + N_* δ < 16 + 9766262 · 0.014355292977070041432 = 140213.5523008260… < 140214`.

## Main results

* `CollatzPosDens.sixteen_add_generationThreshold_mul_logGrowthRate_lt`:
  `16 + N_* δ < 140214`.
-/

@[expose] public section

namespace CollatzPosDens

/-- `16 + N_* δ < 140214`, where `N_*` is `generationThreshold` and `δ` is `logGrowthRate`. -/
@[collatz_pos_dens "lem_ph_endpoint"]
theorem sixteen_add_generationThreshold_mul_logGrowthRate_lt :
    16 + (generationThreshold : ℝ) * logGrowthRate < 140214 := by
  obtain ⟨-, h⟩ := logGrowthRate_mem_Ioo
  rw [generationThreshold_eq]
  push_cast
  linarith

end CollatzPosDens
