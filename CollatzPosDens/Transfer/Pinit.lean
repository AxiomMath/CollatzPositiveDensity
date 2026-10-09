/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Notation

/-!
# The initial schedule time `p_init`

This file defines the natural number `p_init = 1024 = 2^10`, the initial time of a schedule of
times, and records its elementary numerical properties.

## Main definitions

* `CollatzPosDens.pInit`: the natural number `p_init = 1024`.

## Main results

* `CollatzPosDens.pInit_def`: `p_init = 1024`.
* `CollatzPosDens.pInit_eq_two_pow`: `p_init = 2^10`.
* `CollatzPosDens.pInit_add_one`: `p_init + 1 = 1025`.
* `CollatzPosDens.pInit_pos`: `0 < p_init`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The initial schedule time `p_init = 1024`. -/
@[collatz_pos_dens "def_s02_pinit"]
def pInit : ℕ := 1024

/-- The initial schedule time equals `1024`. -/
theorem pInit_def : pInit = 1024 := rfl

/-- The initial schedule time equals `2 ^ 10`. -/
theorem pInit_eq_two_pow : pInit = 2 ^ 10 := rfl

/-- The successor of the initial schedule time is `1025`. -/
theorem pInit_add_one : pInit + 1 = 1025 := rfl

/-- The initial schedule time is positive. -/
theorem pInit_pos : 0 < pInit := by decide

end CollatzPosDens
