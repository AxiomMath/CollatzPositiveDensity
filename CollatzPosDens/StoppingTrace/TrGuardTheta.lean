/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrMu
public import CollatzPosDens.StoppingTrace.TrTheta
public import CollatzPosDens.StoppingTrace.TrMuValue

/-!
# The white-bridge floor is below eight adjacent surpluses

The white-bridge floor `θ_∘ = (10000/3299) μ_∘` satisfies `θ_∘ < 8 μ_∘`. This follows from
`10000/3299 < 8` together with the positivity of the adjacent surplus `μ_∘`, which is read off
its exact value.

## Main results

* `CollatzPosDens.trTheta_lt`: `θ_∘ < 8 μ_∘`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The white-bridge floor is below eight adjacent surpluses: `θ_∘ < 8 μ_∘`. -/
@[collatz_pos_dens "lem_tr_guard_theta"]
theorem trTheta_lt : trTheta < 8 * trMu := by
  rw [trTheta_def]
  have := trMu_pos
  linarith

/-- The white-bridge floor is positive. -/
theorem trTheta_pos : 0 < trTheta := by
  rw [trTheta_def]
  exact mul_pos (by norm_num) trMu_pos

/-- The white-bridge floor is nonnegative. -/
theorem trTheta_nonneg : 0 ≤ trTheta :=
  trTheta_pos.le

end CollatzPosDens
