/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02ROmega
public import CollatzPosDens.Transfer.S02VLower

/-!
# The value of the far-gap scale `R_Ω`

At the original index, `V_*(o) = p_9(o) + 1 = 141268071302011590394`, and
`1231 V_*(o) = 173900995772776267775014 = 4 · 43475248943194066943753 + 2`, so the far-gap scale
is `R_Ω(o) = ⌈1231 V_*(o) / 4⌉ = 43475248943194066943754`. At the bootstrap index,
`V_*(b) = p_2(b) + 1 = 514218`, so `R_Ω(b) = 45 · 514218 = 23139810`.

## Main results

* `CollatzPosDens.ROmega_value_o`: `R_Ω(o) = 43475248943194066943754`.
* `CollatzPosDens.ROmega_value_b`: `R_Ω(b) = 23139810`.

## Implementation notes

The two values are stated as one theorem per index. The values of `V_*` are `Vstar_o` and
`Vstar_b`, read off the schedule positions; `R_Ω(o)` is computed from the natural-number form
`R_Ω(o) = (1231 V_*(o) + 3) / 4` of its definition (`ROmega_o_eq_div`).
-/

@[expose] public section

namespace CollatzPosDens

/-- The far-gap scale at the original index: `R_Ω(o) = ⌈(1231/4) V_*(o)⌉ =
43475248943194066943754`. -/
@[collatz_pos_dens "lem_s02_ROmega_value"]
theorem ROmega_value_o : ROmega .o = 43475248943194066943754 := by
  rw [ROmega_o_eq_div, Vstar_o]

/-- The far-gap scale at the bootstrap index: `R_Ω(b) = 45 V_*(b) = 23139810`. -/
@[collatz_pos_dens "lem_s02_ROmega_value"]
theorem ROmega_value_b : ROmega .b = 23139810 := by
  rw [ROmega_b, Vstar_b]

end CollatzPosDens
