/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Tactic.NormNum

/-!
# The mixing gate level

This file defines the mixing gate level `n₀ = 2^80`, the natural-number threshold on word lengths
beyond which the propagation mixing profile is controlled.

## Main definitions

* `CollatzPosDens.mxGateLevel`: the natural number `n₀ = 2^80`.

## Main results

* `CollatzPosDens.mxGateLevel_def`: `n₀ = 2^80`.
* `CollatzPosDens.mxGateLevel_pos`: `0 < n₀`.
* `CollatzPosDens.one_le_mxGateLevel`: `1 ≤ n₀`.

## Implementation notes

The constant is used only as a threshold `n ≥ n₀` and as a bound, so it is stated as an ordinary
definition; facts about it follow from `mxGateLevel_def`.
-/
@[expose] public section

namespace CollatzPosDens

/-- The mixing gate level `n₀ := 2^80 ∈ ℕ`, the threshold on word lengths for the propagation
mixing profile. -/
@[collatz_pos_dens "def_mx_gate"]
def mxGateLevel : ℕ := 2 ^ 80

/-- The mixing gate level equals `2^80`. -/
theorem mxGateLevel_def : mxGateLevel = 2 ^ 80 := rfl

/-- The mixing gate level is positive. -/
theorem mxGateLevel_pos : 0 < mxGateLevel := by
  rw [mxGateLevel_def]; exact pow_pos (by norm_num) _

/-- The mixing gate level is at least `1`. -/
theorem one_le_mxGateLevel : 1 ≤ mxGateLevel := mxGateLevel_pos

end CollatzPosDens
