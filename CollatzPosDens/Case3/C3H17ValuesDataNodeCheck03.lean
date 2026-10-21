/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNode

/-!
# Checks of the rounded future costs at level 3

The `16` checks `nodeCheck 3 (2048 p) 2048 = true`, `p < 16`, of the recorded values
`10^8 cf⁺_{3}(3^J)`, `J < 2^15`, each evaluated by the kernel.

## Main results

* `CollatzPosDens.C3H17Values.nodeCheck_3`: all `16` checks of level `3`.
-/

set_option Elab.async false

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- The check of the recorded values of level `3` at the `2048` points from `0` succeeds. -/
theorem nodeCheck_3_0 : nodeCheck 3 0 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `2048` succeeds. -/
theorem nodeCheck_3_1 : nodeCheck 3 2048 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `4096` succeeds. -/
theorem nodeCheck_3_2 : nodeCheck 3 4096 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `6144` succeeds. -/
theorem nodeCheck_3_3 : nodeCheck 3 6144 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `8192` succeeds. -/
theorem nodeCheck_3_4 : nodeCheck 3 8192 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `10240` succeeds. -/
theorem nodeCheck_3_5 : nodeCheck 3 10240 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `12288` succeeds. -/
theorem nodeCheck_3_6 : nodeCheck 3 12288 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `14336` succeeds. -/
theorem nodeCheck_3_7 : nodeCheck 3 14336 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `16384` succeeds. -/
theorem nodeCheck_3_8 : nodeCheck 3 16384 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `18432` succeeds. -/
theorem nodeCheck_3_9 : nodeCheck 3 18432 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `20480` succeeds. -/
theorem nodeCheck_3_10 : nodeCheck 3 20480 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `22528` succeeds. -/
theorem nodeCheck_3_11 : nodeCheck 3 22528 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `24576` succeeds. -/
theorem nodeCheck_3_12 : nodeCheck 3 24576 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `26624` succeeds. -/
theorem nodeCheck_3_13 : nodeCheck 3 26624 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `28672` succeeds. -/
theorem nodeCheck_3_14 : nodeCheck 3 28672 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The check of the recorded values of level `3` at the `2048` points from `30720` succeeds. -/
theorem nodeCheck_3_15 : nodeCheck 3 30720 2048 = true :=
  nodeCheck_of_nodeCheckF (by decide +kernel)

/-- The checks of the recorded values of level `3` at the points `2048 p, …, 2048 p + 2047`
succeed for every `p < 16`. -/
theorem nodeCheck_3 : ∀ p < 16, nodeCheck 3 (2048 * p) 2048 = true := by
  intro p hp
  interval_cases p
  · exact nodeCheck_3_0
  · exact nodeCheck_3_1
  · exact nodeCheck_3_2
  · exact nodeCheck_3_3
  · exact nodeCheck_3_4
  · exact nodeCheck_3_5
  · exact nodeCheck_3_6
  · exact nodeCheck_3_7
  · exact nodeCheck_3_8
  · exact nodeCheck_3_9
  · exact nodeCheck_3_10
  · exact nodeCheck_3_11
  · exact nodeCheck_3_12
  · exact nodeCheck_3_13
  · exact nodeCheck_3_14
  · exact nodeCheck_3_15

end C3H17Values

end CollatzPosDens
