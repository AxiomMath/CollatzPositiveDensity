/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNode

/-!
# Checks of the rounded future costs at level 12

The `16` checks `nodeCheck 12 (2048 p) 2048 = true`, `p < 16`, of the recorded values
`10^8 cf⁺_{12}(3^J)`, `J < 2^15`, each evaluated by the kernel.

## Main results

* `CollatzPosDens.C3H17Values.nodeCheck_12`: all `16` checks of level `12`.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the recorded values of level `12` at the points `0, …, 2047` succeeds. -/
theorem nodeCheck_12_0 : nodeCheck 12 0 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `2048, …, 4095` succeeds. -/
theorem nodeCheck_12_1 : nodeCheck 12 2048 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `4096, …, 6143` succeeds. -/
theorem nodeCheck_12_2 : nodeCheck 12 4096 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `6144, …, 8191` succeeds. -/
theorem nodeCheck_12_3 : nodeCheck 12 6144 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `8192, …, 10239` succeeds. -/
theorem nodeCheck_12_4 : nodeCheck 12 8192 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `10240, …, 12287` succeeds. -/
theorem nodeCheck_12_5 : nodeCheck 12 10240 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `12288, …, 14335` succeeds. -/
theorem nodeCheck_12_6 : nodeCheck 12 12288 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `14336, …, 16383` succeeds. -/
theorem nodeCheck_12_7 : nodeCheck 12 14336 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `16384, …, 18431` succeeds. -/
theorem nodeCheck_12_8 : nodeCheck 12 16384 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `18432, …, 20479` succeeds. -/
theorem nodeCheck_12_9 : nodeCheck 12 18432 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `20480, …, 22527` succeeds. -/
theorem nodeCheck_12_10 : nodeCheck 12 20480 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `22528, …, 24575` succeeds. -/
theorem nodeCheck_12_11 : nodeCheck 12 22528 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `24576, …, 26623` succeeds. -/
theorem nodeCheck_12_12 : nodeCheck 12 24576 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `26624, …, 28671` succeeds. -/
theorem nodeCheck_12_13 : nodeCheck 12 26624 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `28672, …, 30719` succeeds. -/
theorem nodeCheck_12_14 : nodeCheck 12 28672 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `12` at the points `30720, …, 32767` succeeds. -/
theorem nodeCheck_12_15 : nodeCheck 12 30720 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- For every `p < 16`, the check of the recorded values of level `12` at the points
`2048 p, …, 2048 p + 2047` succeeds. -/
theorem nodeCheck_12 : ∀ p < 16, nodeCheck 12 (2048 * p) 2048 = true := by
  intro p hp
  interval_cases p
  · exact nodeCheck_12_0
  · exact nodeCheck_12_1
  · exact nodeCheck_12_2
  · exact nodeCheck_12_3
  · exact nodeCheck_12_4
  · exact nodeCheck_12_5
  · exact nodeCheck_12_6
  · exact nodeCheck_12_7
  · exact nodeCheck_12_8
  · exact nodeCheck_12_9
  · exact nodeCheck_12_10
  · exact nodeCheck_12_11
  · exact nodeCheck_12_12
  · exact nodeCheck_12_13
  · exact nodeCheck_12_14
  · exact nodeCheck_12_15

end C3H17Values

end CollatzPosDens
