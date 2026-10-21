/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNode

/-!
# Checks of the rounded future costs at level 4

The `16` checks `nodeCheck 4 (2048 p) 2048 = true`, `p < 16`, of the recorded values
`10^8 cf⁺_{4}(3^J)`, `J < 2^15`, each evaluated by the kernel.

## Main results

* `CollatzPosDens.C3H17Values.nodeCheck_4`: all `16` checks of level `4`.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the recorded values of level `4` at the `2048` points from `0`. -/
theorem nodeCheck_4_0 : nodeCheck 4 0 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `2048`. -/
theorem nodeCheck_4_1 : nodeCheck 4 2048 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `4096`. -/
theorem nodeCheck_4_2 : nodeCheck 4 4096 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `6144`. -/
theorem nodeCheck_4_3 : nodeCheck 4 6144 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `8192`. -/
theorem nodeCheck_4_4 : nodeCheck 4 8192 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `10240`. -/
theorem nodeCheck_4_5 : nodeCheck 4 10240 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `12288`. -/
theorem nodeCheck_4_6 : nodeCheck 4 12288 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `14336`. -/
theorem nodeCheck_4_7 : nodeCheck 4 14336 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `16384`. -/
theorem nodeCheck_4_8 : nodeCheck 4 16384 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `18432`. -/
theorem nodeCheck_4_9 : nodeCheck 4 18432 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `20480`. -/
theorem nodeCheck_4_10 : nodeCheck 4 20480 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `22528`. -/
theorem nodeCheck_4_11 : nodeCheck 4 22528 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `24576`. -/
theorem nodeCheck_4_12 : nodeCheck 4 24576 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `26624`. -/
theorem nodeCheck_4_13 : nodeCheck 4 26624 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `28672`. -/
theorem nodeCheck_4_14 : nodeCheck 4 28672 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `4` at the `2048` points from `30720`. -/
theorem nodeCheck_4_15 : nodeCheck 4 30720 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The checks of the recorded values of level `4` at the points `2048 p, …, 2048 p + 2047`
succeed for every `p < 16`. -/
theorem nodeCheck_4 : ∀ p < 16, nodeCheck 4 (2048 * p) 2048 = true := by
  intro p hp
  interval_cases p
  · exact nodeCheck_4_0
  · exact nodeCheck_4_1
  · exact nodeCheck_4_2
  · exact nodeCheck_4_3
  · exact nodeCheck_4_4
  · exact nodeCheck_4_5
  · exact nodeCheck_4_6
  · exact nodeCheck_4_7
  · exact nodeCheck_4_8
  · exact nodeCheck_4_9
  · exact nodeCheck_4_10
  · exact nodeCheck_4_11
  · exact nodeCheck_4_12
  · exact nodeCheck_4_13
  · exact nodeCheck_4_14
  · exact nodeCheck_4_15

end C3H17Values

end CollatzPosDens
