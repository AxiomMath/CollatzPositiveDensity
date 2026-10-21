/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNode

/-!
# Checks of the rounded future costs at level 2

The `16` checks `nodeCheck 2 (2048 p) 2048 = true`, `p < 16`, of the recorded values
`10^8 cf⁺_{2}(3^J)`, `J < 2^15`, each evaluated by the kernel.

## Main results

* `CollatzPosDens.C3H17Values.nodeCheck_2`: all `16` checks of level `2`.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the recorded values of level `2` succeeds at the points `0, …, 2047`. -/
theorem nodeCheck_2_0 : nodeCheck 2 0 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `2048, …, 4095`. -/
theorem nodeCheck_2_1 : nodeCheck 2 2048 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `4096, …, 6143`. -/
theorem nodeCheck_2_2 : nodeCheck 2 4096 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `6144, …, 8191`. -/
theorem nodeCheck_2_3 : nodeCheck 2 6144 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `8192, …, 10239`. -/
theorem nodeCheck_2_4 : nodeCheck 2 8192 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `10240, …, 12287`. -/
theorem nodeCheck_2_5 : nodeCheck 2 10240 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `12288, …, 14335`. -/
theorem nodeCheck_2_6 : nodeCheck 2 12288 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `14336, …, 16383`. -/
theorem nodeCheck_2_7 : nodeCheck 2 14336 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `16384, …, 18431`. -/
theorem nodeCheck_2_8 : nodeCheck 2 16384 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `18432, …, 20479`. -/
theorem nodeCheck_2_9 : nodeCheck 2 18432 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `20480, …, 22527`. -/
theorem nodeCheck_2_10 : nodeCheck 2 20480 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `22528, …, 24575`. -/
theorem nodeCheck_2_11 : nodeCheck 2 22528 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `24576, …, 26623`. -/
theorem nodeCheck_2_12 : nodeCheck 2 24576 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `26624, …, 28671`. -/
theorem nodeCheck_2_13 : nodeCheck 2 26624 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `28672, …, 30719`. -/
theorem nodeCheck_2_14 : nodeCheck 2 28672 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points `30720, …, 32767`. -/
theorem nodeCheck_2_15 : nodeCheck 2 30720 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `2` succeeds at the points
`2048 p, …, 2048 p + 2047` for every `p < 16`. -/
theorem nodeCheck_2 : ∀ p < 16, nodeCheck 2 (2048 * p) 2048 = true := by
  intro p hp
  interval_cases p
  · exact nodeCheck_2_0
  · exact nodeCheck_2_1
  · exact nodeCheck_2_2
  · exact nodeCheck_2_3
  · exact nodeCheck_2_4
  · exact nodeCheck_2_5
  · exact nodeCheck_2_6
  · exact nodeCheck_2_7
  · exact nodeCheck_2_8
  · exact nodeCheck_2_9
  · exact nodeCheck_2_10
  · exact nodeCheck_2_11
  · exact nodeCheck_2_12
  · exact nodeCheck_2_13
  · exact nodeCheck_2_14
  · exact nodeCheck_2_15

end C3H17Values

end CollatzPosDens
