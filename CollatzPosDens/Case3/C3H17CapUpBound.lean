/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CapRange
public import CollatzPosDens.Case3.C3H17CapUp
public import CollatzPosDens.StoppingTrace.TrCapUpperLem

/-!
# The grid majorant dominates the capped packet factor

For every integer `c` and rational `θ`, the capped packet factor `Φ^cap_c(θ)`
(`CollatzPosDens.trCapFactor`) is at most the grid majorant `Ū_c(θ)`
(`CollatzPosDens.c3H17CapUp`).

For `3 ≤ c ≤ 16` the rational majorant `CollatzPosDens.trCapFactor_le_trCapUpper` gives
`Φ^cap_c(θ) ≤ U^{10^{-18}}_c(θ)`, hence `Φ^cap_c(θ) ≤ max (U^{10^{-18}}_c(θ), 1526 / 10^8)`;
together with `Φ^cap_c(θ) ≤ 1` this bounds `Φ^cap_c(θ)` by the minimum of the two, which is
`Ū_c(θ)`. Otherwise both sides equal `1`.

## Main results

* `CollatzPosDens.trCapFactor_le_c3H17CapUp`: `Φ^cap_c(θ) ≤ Ū_c(θ)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The grid majorant dominates the capped packet factor.** For every integer `c` and rational
`θ`, `Φ^cap_c(θ) ≤ Ū_c(θ)`. -/
@[collatz_pos_dens "lem_c3_h17_cap_up_bound"]
theorem trCapFactor_le_c3H17CapUp (c : ℤ) (θ : ℚ) :
    trCapFactor c θ ≤ c3H17CapUp c θ := by
  by_cases h : 3 ≤ c ∧ c ≤ 16
  · rw [c3H17CapUp_of_mem h.1 h.2, Rat.cast_min, Rat.cast_max, Rat.cast_one]
    exact le_min (trCapFactor_mem_Icc c θ).2
      (le_max_of_le_left (trCapFactor_le_trCapUpper c _ θ))
  · rw [trCapFactor_of_not_mem h, c3H17CapUp_of_not_mem h, Rat.cast_one]

end CollatzPosDens
