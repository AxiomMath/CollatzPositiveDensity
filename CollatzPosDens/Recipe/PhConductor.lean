/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.S04QstarGe
public import CollatzPosDens.Recipe.PhH0Large

/-!
# The length sum up to the generation threshold is below the conductor

The total length of the words read in the first `N_*` generations is below the conductor:
$$k_{N_*} + \sum_{j<N_*} \mathrm{len}^+(b_j) < q_*.$$

Indeed the left side is less than `1668728 𝗀^{N_*}`
(`level_generationThreshold_add_sum_lenPlus_lt`), which is less than
`q_* = ⌈1668728 · (101/100)^{N_*}⌉` (`logb_two_seedBound_gt`).

## Main results

* `CollatzPosDens.logb_conductor_add_one_lt`: `k_{N_*} + ∑_{j<N_*} len⁺(b_j) < q_*`.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The length sum up to generation `N_*` is below the conductor:
`k_{N_*} + ∑_{j<N_*} len⁺(b_j) < q_*`. -/
@[collatz_pos_dens "lem_ph_conductor"]
theorem logb_conductor_add_one_lt :
    level generationThreshold + ∑ j ∈ range generationThreshold, lenPlus (scale j) <
      conductor := by
  have h := level_generationThreshold_add_sum_lenPlus_lt.trans logb_two_seedBound_gt
  exact_mod_cast h

end CollatzPosDens
