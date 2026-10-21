/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNode

/-!
# Checks of the rounded future costs at level 6

The `16` checks `nodeCheck 6 (2048 p) 2048 = true`, `p < 16`, of the recorded values
`10^8 cf⁺_{6}(3^J)`, `J < 2^15`, each evaluated by the kernel.

## Main results

* `CollatzPosDens.C3H17Values.nodeCheck_6`: all `16` checks of level `6`.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the recorded values at the `2048` points `0, …, 2047` of level `6` passes. -/
theorem nodeCheck_6_0 : nodeCheck 6 0 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `2048, …, 4095` of level `6` passes. -/
theorem nodeCheck_6_1 : nodeCheck 6 2048 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `4096, …, 6143` of level `6` passes. -/
theorem nodeCheck_6_2 : nodeCheck 6 4096 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `6144, …, 8191` of level `6` passes. -/
theorem nodeCheck_6_3 : nodeCheck 6 6144 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `8192, …, 10239` of level `6` passes. -/
theorem nodeCheck_6_4 : nodeCheck 6 8192 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `10240, …, 12287` of level `6` passes. -/
theorem nodeCheck_6_5 : nodeCheck 6 10240 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `12288, …, 14335` of level `6` passes. -/
theorem nodeCheck_6_6 : nodeCheck 6 12288 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `14336, …, 16383` of level `6` passes. -/
theorem nodeCheck_6_7 : nodeCheck 6 14336 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `16384, …, 18431` of level `6` passes. -/
theorem nodeCheck_6_8 : nodeCheck 6 16384 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `18432, …, 20479` of level `6` passes. -/
theorem nodeCheck_6_9 : nodeCheck 6 18432 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `20480, …, 22527` of level `6` passes. -/
theorem nodeCheck_6_10 : nodeCheck 6 20480 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `22528, …, 24575` of level `6` passes. -/
theorem nodeCheck_6_11 : nodeCheck 6 22528 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `24576, …, 26623` of level `6` passes. -/
theorem nodeCheck_6_12 : nodeCheck 6 24576 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `26624, …, 28671` of level `6` passes. -/
theorem nodeCheck_6_13 : nodeCheck 6 26624 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `28672, …, 30719` of level `6` passes. -/
theorem nodeCheck_6_14 : nodeCheck 6 28672 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the `2048` points `30720, …, 32767` of level `6` passes. -/
theorem nodeCheck_6_15 : nodeCheck 6 30720 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values at the points `2048 p, …, 2048 p + 2047` of level `6` passes
for every `p < 16`. -/
theorem nodeCheck_6 : ∀ p < 16, nodeCheck 6 (2048 * p) 2048 = true := by
  intro p hp
  interval_cases p
  · exact nodeCheck_6_0
  · exact nodeCheck_6_1
  · exact nodeCheck_6_2
  · exact nodeCheck_6_3
  · exact nodeCheck_6_4
  · exact nodeCheck_6_5
  · exact nodeCheck_6_6
  · exact nodeCheck_6_7
  · exact nodeCheck_6_8
  · exact nodeCheck_6_9
  · exact nodeCheck_6_10
  · exact nodeCheck_6_11
  · exact nodeCheck_6_12
  · exact nodeCheck_6_13
  · exact nodeCheck_6_14
  · exact nodeCheck_6_15

end C3H17Values

end CollatzPosDens
