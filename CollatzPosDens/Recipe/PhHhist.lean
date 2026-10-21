/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# The histogram constant `𝓗_hist`

The histogram constant `𝓗_hist`, written `Hhist`, is the rational number `344`. It is an integer
upper bound for the rational number `(97/128) · (37170/82) = 1802745/5248 = 343.51…`.

## Main definitions

* `CollatzPosDens.Hhist`: the histogram constant `344 ∈ ℚ`.

## Main results

* `CollatzPosDens.Hhist_def`: `𝓗_hist = 344`.
* `CollatzPosDens.Hhist_pos`: `0 < 𝓗_hist`.
* `CollatzPosDens.Hhist_cast`: the real cast of `𝓗_hist` is `344`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The histogram constant `𝓗_hist := 344 ∈ ℚ`. -/
@[collatz_pos_dens "def_ph_Hhist"]
def Hhist : ℚ := 344

/-- The defining value `𝓗_hist = 344`. -/
theorem Hhist_def : Hhist = 344 := rfl

/-- The histogram constant is positive. -/
theorem Hhist_pos : 0 < Hhist := by
  norm_num [Hhist]

/-- The real cast of the histogram constant. -/
@[simp]
theorem Hhist_cast : ((Hhist : ℚ) : ℝ) = 344 := by
  norm_num [Hhist]

end CollatzPosDens
