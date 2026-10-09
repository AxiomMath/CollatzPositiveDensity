/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# The physical growth ratio `𝗀`

The physical growth ratio is the rational number
$$\mathsf g = \frac{101}{100} \in \mathbb{Q}.$$
This file defines `𝗀` and records its value, its positivity, `1 < 𝗀`, and the same facts
after casting to `ℝ`.

## Main definitions

* `CollatzPosDens.growthRatio`: the physical growth ratio `𝗀 = 101/100`.

## Main results

* `CollatzPosDens.growthRatio_def`: `𝗀 = 101/100`.
* `CollatzPosDens.growthRatio_pos`, `CollatzPosDens.one_lt_growthRatio`: `0 < 𝗀`, `1 < 𝗀`.
* `CollatzPosDens.growthRatio_cast`: `(𝗀 : ℝ) = 101/100`, with real positivity and `1 < 𝗀`.

## Implementation notes

`𝗀` is a rational number; real-valued statements use the cast `(𝗀 : ℝ)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The physical growth ratio `𝗀 = 101/100 ∈ ℚ`. -/
@[collatz_pos_dens "def_ph_ratio"]
def growthRatio : ℚ := 101 / 100

/-- The growth ratio `𝗀` equals `101/100`. -/
theorem growthRatio_def : growthRatio = 101 / 100 := rfl

/-- The growth ratio `𝗀` is positive. -/
theorem growthRatio_pos : 0 < growthRatio := by norm_num [growthRatio]

/-- The growth ratio `𝗀` is greater than `1`. -/
theorem one_lt_growthRatio : 1 < growthRatio := by norm_num [growthRatio]

/-- The real cast of the growth ratio `𝗀` equals `101/100`. -/
theorem growthRatio_cast : (growthRatio : ℝ) = 101 / 100 := by
  rw [growthRatio_def]; norm_num

/-- The real cast of the growth ratio `𝗀` is positive. -/
theorem growthRatio_cast_pos : 0 < (growthRatio : ℝ) := Rat.cast_pos.mpr growthRatio_pos

/-- The real cast of the growth ratio `𝗀` is greater than `1`. -/
theorem one_lt_growthRatio_cast : 1 < (growthRatio : ℝ) := by
  exact_mod_cast one_lt_growthRatio

end CollatzPosDens
