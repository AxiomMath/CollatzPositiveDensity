/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Notation

/-!
# The generation threshold `N_*`

This file defines the generation threshold, the natural number `N_* := 9853`, and records its
value and its positivity.

## Main definitions

* `CollatzPosDens.generationThreshold`: the threshold `N_* ∈ ℕ`.

## Main results

* `CollatzPosDens.generationThreshold_def`: `N_* = 9853`.
* `CollatzPosDens.generationThreshold_pos`: `0 < N_*`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The generation threshold `N_* := 9853 ∈ ℕ`. -/
@[collatz_pos_dens "def_Nstar"]
def generationThreshold : ℕ := 9853

/-- The value of the generation threshold. -/
theorem generationThreshold_def : generationThreshold = 9853 := rfl

/-- The generation threshold is positive. -/
theorem generationThreshold_pos : 0 < generationThreshold := by
  rw [generationThreshold_def]; decide

end CollatzPosDens
