/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNode

/-!
# Checks of the rounded future costs at level 9

The `16` checks `nodeCheck 9 (2048 p) 2048 = true`, `p < 16`, of the recorded values
`10^8 cf⁺_{9}(3^J)`, `J < 2^15`, each evaluated by the kernel.

## Main results

* `CollatzPosDens.C3H17Values.nodeCheck_9`: all `16` checks of level `9`.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the recorded values at the points `0, …, 2047` of level `9` passes. -/
theorem nodeCheck_9_0 : nodeCheck 9 0 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `2048, …, 4095` of level `9` passes. -/
theorem nodeCheck_9_1 : nodeCheck 9 2048 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `4096, …, 6143` of level `9` passes. -/
theorem nodeCheck_9_2 : nodeCheck 9 4096 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `6144, …, 8191` of level `9` passes. -/
theorem nodeCheck_9_3 : nodeCheck 9 6144 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `8192, …, 10239` of level `9` passes. -/
theorem nodeCheck_9_4 : nodeCheck 9 8192 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `10240, …, 12287` of level `9` passes. -/
theorem nodeCheck_9_5 : nodeCheck 9 10240 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `12288, …, 14335` of level `9` passes. -/
theorem nodeCheck_9_6 : nodeCheck 9 12288 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `14336, …, 16383` of level `9` passes. -/
theorem nodeCheck_9_7 : nodeCheck 9 14336 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `16384, …, 18431` of level `9` passes. -/
theorem nodeCheck_9_8 : nodeCheck 9 16384 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `18432, …, 20479` of level `9` passes. -/
theorem nodeCheck_9_9 : nodeCheck 9 18432 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `20480, …, 22527` of level `9` passes. -/
theorem nodeCheck_9_10 : nodeCheck 9 20480 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `22528, …, 24575` of level `9` passes. -/
theorem nodeCheck_9_11 : nodeCheck 9 22528 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `24576, …, 26623` of level `9` passes. -/
theorem nodeCheck_9_12 : nodeCheck 9 24576 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `26624, …, 28671` of level `9` passes. -/
theorem nodeCheck_9_13 : nodeCheck 9 26624 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `28672, …, 30719` of level `9` passes. -/
theorem nodeCheck_9_14 : nodeCheck 9 28672 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `30720, …, 32767` of level `9` passes. -/
theorem nodeCheck_9_15 : nodeCheck 9 30720 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- For every `p < 16`, the check of the recorded values at the points
`2048 p, …, 2048 p + 2047` of level `9` passes. -/
theorem nodeCheck_9 : ∀ p < 16, nodeCheck 9 (2048 * p) 2048 = true := by
  intro p hp
  interval_cases p
  · exact nodeCheck_9_0
  · exact nodeCheck_9_1
  · exact nodeCheck_9_2
  · exact nodeCheck_9_3
  · exact nodeCheck_9_4
  · exact nodeCheck_9_5
  · exact nodeCheck_9_6
  · exact nodeCheck_9_7
  · exact nodeCheck_9_8
  · exact nodeCheck_9_9
  · exact nodeCheck_9_10
  · exact nodeCheck_9_11
  · exact nodeCheck_9_12
  · exact nodeCheck_9_13
  · exact nodeCheck_9_14
  · exact nodeCheck_9_15

end C3H17Values

end CollatzPosDens
