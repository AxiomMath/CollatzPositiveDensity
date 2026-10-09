/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.Scales
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The conductor `q_*`

The conductor is the natural number
$$q_* := k_{N_*} + \sum_{j=0}^{N_*-1} h_{b_j},$$
where `N_*` is the generation threshold, `b_j` the scales, `k_n = ⌊b_n/4⌋` the residue levels
and `h_b = b + ⌊3b/5⌋` the scale parameter.

## Main definitions

* `CollatzPosDens.conductorAt`: the expression `k_N + ∑_{j<N} h_{b_j}` as a function of `N`.
* `CollatzPosDens.conductor`: the conductor `q_*`, its value at `N = N_*`.

## Main results

* `CollatzPosDens.conductor_def`: the defining formula of `q_*`.
* `CollatzPosDens.level_le_conductor`: `k_{N_*} ≤ q_*`.
* `CollatzPosDens.sum_hb_le_conductor`: `∑_{j<N_*} h_{b_j} ≤ q_*`.
* `CollatzPosDens.conductor_pos`: `0 < q_*`.

## Implementation notes

The conductor is the value at `N_*` of the parametric expression `conductorAt`, which is defined
for every natural number `N`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The expression `k_N + ∑_{j<N} h_{b_j}`; the conductor `q_*` is its value at `N = N_*`. -/
def conductorAt (N : ℕ) : ℕ := level N + ∑ j ∈ range N, hb (scale j)

/-- The defining formula of `conductorAt`. -/
theorem conductorAt_def (N : ℕ) : conductorAt N = level N + ∑ j ∈ range N, hb (scale j) := rfl

/-- **The conductor** `q_* := k_{N_*} + ∑_{j=0}^{N_*-1} h_{b_j} ∈ ℕ`. -/
@[collatz_pos_dens "def_qstar"]
noncomputable def conductor : ℕ := conductorAt generationThreshold

/-- `q_*` is `conductorAt` at the generation threshold `N_*`. -/
theorem conductor_eq_conductorAt : conductor = conductorAt generationThreshold := rfl

/-- The defining formula `q_* = k_{N_*} + ∑_{j<N_*} h_{b_j}`. -/
theorem conductor_def :
    conductor = level generationThreshold + ∑ j ∈ range generationThreshold, hb (scale j) := rfl

/-- `k_{N_*} ≤ q_*`. -/
theorem level_le_conductor : level generationThreshold ≤ conductor :=
  Nat.le_add_right _ _

/-- `∑_{j<N_*} h_{b_j} ≤ q_*`. -/
theorem sum_hb_le_conductor : ∑ j ∈ range generationThreshold, hb (scale j) ≤ conductor :=
  Nat.le_add_left _ _

/-- The conductor is positive. -/
theorem conductor_pos : 0 < conductor :=
  lt_of_lt_of_le (level_pos _) level_le_conductor

end CollatzPosDens
