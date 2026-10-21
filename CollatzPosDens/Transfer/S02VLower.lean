/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02B
public import CollatzPosDens.Transfer.S02ScheduleValues

/-!
# A lower bound for the active packing bound `V_*`

Since `r_*(o) = 10` and `r_*(b) = 3`, the active packing bounds are `V_*(o) = p_9(o) + 1` and
`V_*(b) = p_2(b) + 1`, and the exact values of the schedule positions give
`V_*(o) = 141268071302011590394` and `V_*(b) = 514218`. Both are at least `2^{18} = 262144`, so
`2^{18} ≤ V_*(ι)` for every index `ι`. At the original index the stronger bound
`2^{66} ≤ V_*(o)` holds; it fails at the bootstrap index.

## Main results

* `CollatzPosDens.Vstar_o`, `CollatzPosDens.Vstar_b`: the exact values of `V_*(o)` and `V_*(b)`.
* `CollatzPosDens.two_pow_18_le_Vstar`: `2^{18} ≤ V_*(ι)`.
* `CollatzPosDens.two_pow_66_le_Vstar_o`: `2^{66} ≤ V_*(o)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of the active packing bound `V_*(o) = p_9(o) + 1`. -/
theorem Vstar_o : Vstar .o = 141268071302011590394 := by
  have h : schedule .o 9 = 141268071302011590393 := by
    simpa using congrArg (fun l : List ℕ => l.getD 9 0) schedule_values_o
  rw [Vstar_o_eq, h]

/-- The exact value of the active packing bound `V_*(b) = p_2(b) + 1`. -/
theorem Vstar_b : Vstar .b = 514218 := by
  have h : schedule .b 2 = 514217 := by
    simpa using congrArg (fun l : List ℕ => l.getD 2 0) schedule_values_b
  rw [Vstar_b_eq, h]

/-- **Lower size of the active packing bound.** `2^{18} ≤ V_*(ι)` for every index `ι`. -/
@[collatz_pos_dens "lem_s02_V_lower"]
theorem two_pow_18_le_Vstar (ι : FIndex) : 2 ^ 18 ≤ Vstar ι := by
  cases ι
  · rw [Vstar_o]
    norm_num
  · rw [Vstar_b]
    norm_num

/-- At the original index, `2^{66} ≤ V_*(o)`. -/
theorem two_pow_66_le_Vstar_o : 2 ^ 66 ≤ Vstar .o := by
  rw [Vstar_o]
  norm_num

end CollatzPosDens
