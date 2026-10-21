/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapFactor

/-!
# Range of the capped packet factor

For every integer `c` and real `θ`, the capped packet factor `Φ^cap_c(θ)`
(`CollatzPosDens.trCapFactor`) lies in the unit interval `[0, 1]`.

For `t ≥ 1` the packet function `Φ_t(θ)` (`CollatzPosDens.chPacketFn`) is `1 / t` times the
modulus of a sum of `t` complex numbers of modulus `1`, so it lies in `[0, 1]` by the triangle
inequality. Hence `Φ^cap_c(θ) = max {Φ_{c-1}(θ), 2^{-16}} ∈ [2^{-16}, 1]` for `3 ≤ c ≤ 16`, and
`Φ^cap_c(θ) = 1` otherwise.

## Main results

* `CollatzPosDens.trCapFactor_mem_Icc`: `0 ≤ Φ^cap_c(θ) ≤ 1`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The capped packet factor lies in the unit interval: `0 ≤ Φ^cap_c(θ) ≤ 1`. -/
@[collatz_pos_dens "lem_c3_cap_range"]
theorem trCapFactor_mem_Icc (c : ℤ) (θ : ℝ) : trCapFactor c θ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(trCapFactor_pos c θ).le, trCapFactor_le_one c θ⟩

end CollatzPosDens
