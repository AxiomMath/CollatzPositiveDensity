/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.FirstCrossing.ScalesGrowth

/-!
# A lower bound for the conductor

The conductor is at least nine times the generation threshold: `9 N_* ≤ q_*`.
By definition `q_* = k_{N_*} + ∑_{j<N_*} h_{b_j}`, so `q_*` is at least the sum, and each term
satisfies `h_{b_j} ≥ b_j ≥ b_0 = 9`, since `h_b ≥ b` and the scales are increasing.

## Main results

* `CollatzPosDens.nine_mul_generationThreshold_le_conductor`: `9 N_* ≤ q_*`.

## Implementation notes

The bound `9 N ≤ k_N + ∑_{j<N} h_{b_j}` holds for every `N`; the statement is its instance at
`N = N_*`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- `9 N ≤ k_N + ∑_{j<N} h_{b_j}` for every `N`. -/
private theorem nine_mul_le_conductorAt (N : ℕ) : 9 * N ≤ conductorAt N := by
  have h : 9 * N ≤ ∑ j ∈ range N, hb (scale j) := by
    simpa [mul_comm] using card_nsmul_le_sum (range N) (fun j => hb (scale j)) 9 fun j _ =>
      (nine_le_scale j).trans (le_hb _)
  rw [conductorAt_def]
  exact h.trans (Nat.le_add_left _ _)

/-- The conductor is at least nine times the generation threshold: `9 N_* ≤ q_*`. -/
@[collatz_pos_dens "lem_s04_qstar_ge"]
theorem nine_mul_generationThreshold_le_conductor : 9 * generationThreshold ≤ conductor :=
  nine_mul_le_conductorAt _

end CollatzPosDens
