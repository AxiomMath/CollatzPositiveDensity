/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNode

/-!
# Checks of the rounded future costs at level 7

The `16` checks `nodeCheck 7 (2048 p) 2048 = true`, `p < 16`, of the recorded values
`10^8 cf⁺_{7}(3^J)`, `J < 2^15`, each evaluated by the kernel.

## Main results

* `CollatzPosDens.C3H17Values.nodeCheck_7`: all `16` checks of level `7`.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the recorded values at the points `0, …, 2047` of level `7` succeeds. -/
theorem nodeCheck_7_0 : nodeCheck 7 0 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `2048, …, 4095` of level `7` succeeds. -/
theorem nodeCheck_7_1 : nodeCheck 7 2048 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `4096, …, 6143` of level `7` succeeds. -/
theorem nodeCheck_7_2 : nodeCheck 7 4096 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `6144, …, 8191` of level `7` succeeds. -/
theorem nodeCheck_7_3 : nodeCheck 7 6144 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `8192, …, 10239` of level `7` succeeds. -/
theorem nodeCheck_7_4 : nodeCheck 7 8192 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `10240, …, 12287` of level `7` succeeds. -/
theorem nodeCheck_7_5 : nodeCheck 7 10240 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `12288, …, 14335` of level `7` succeeds. -/
theorem nodeCheck_7_6 : nodeCheck 7 12288 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `14336, …, 16383` of level `7` succeeds. -/
theorem nodeCheck_7_7 : nodeCheck 7 14336 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `16384, …, 18431` of level `7` succeeds. -/
theorem nodeCheck_7_8 : nodeCheck 7 16384 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `18432, …, 20479` of level `7` succeeds. -/
theorem nodeCheck_7_9 : nodeCheck 7 18432 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `20480, …, 22527` of level `7` succeeds. -/
theorem nodeCheck_7_10 : nodeCheck 7 20480 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `22528, …, 24575` of level `7` succeeds. -/
theorem nodeCheck_7_11 : nodeCheck 7 22528 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `24576, …, 26623` of level `7` succeeds. -/
theorem nodeCheck_7_12 : nodeCheck 7 24576 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `26624, …, 28671` of level `7` succeeds. -/
theorem nodeCheck_7_13 : nodeCheck 7 26624 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `28672, …, 30719` of level `7` succeeds. -/
theorem nodeCheck_7_14 : nodeCheck 7 28672 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `30720, …, 32767` of level `7` succeeds. -/
theorem nodeCheck_7_15 : nodeCheck 7 30720 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- For every `p < 16`, the check of the recorded values at the points `2048 p, …, 2048 p + 2047`
of level `7` succeeds. -/
theorem nodeCheck_7 : ∀ p < 16, nodeCheck 7 (2048 * p) 2048 = true := by
  intro p hp
  interval_cases p
  · exact nodeCheck_7_0
  · exact nodeCheck_7_1
  · exact nodeCheck_7_2
  · exact nodeCheck_7_3
  · exact nodeCheck_7_4
  · exact nodeCheck_7_5
  · exact nodeCheck_7_6
  · exact nodeCheck_7_7
  · exact nodeCheck_7_8
  · exact nodeCheck_7_9
  · exact nodeCheck_7_10
  · exact nodeCheck_7_11
  · exact nodeCheck_7_12
  · exact nodeCheck_7_13
  · exact nodeCheck_7_14
  · exact nodeCheck_7_15

end C3H17Values

end CollatzPosDens
