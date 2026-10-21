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
public import Mathlib.Data.Rat.Floor

/-!
# The conductor `q_*`

The conductor of the recipe is the natural number `q_* := ⌈1668728 · (101/100)^{N_*}⌉`, the
ceiling of an exact rational number, where `N_*` is the generation threshold. The seed is built
modulo `3^{q_*}`, and the only property of `q_*` the construction needs is that it dominates the
total length `k_N + ∑_{j<N} h_{b_j}` of the words read in the first `N` generations, where `b_j`
are the scales, `k_n = ⌊b_n/4⌋` the residue levels and `h_b = b + ⌊3b/5⌋` the scale parameter.

## Main definitions

* `CollatzPosDens.conductorAt`: the total length `k_N + ∑_{j<N} h_{b_j}` as a function of `N`.
* `CollatzPosDens.conductor`: the conductor `q_* = ⌈1668728 · (101/100)^{N_*}⌉`.

## Main results

* `CollatzPosDens.conductor_def`: `q_* = ⌈1668728 · (101/100)^{N_*}⌉`.
* `CollatzPosDens.conductor_pos`: `0 < q_*`.

## Implementation notes

The conductor is a fixed explicit number rather than the total length `conductorAt N_*` itself;
any upper bound on that length serves.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The total length `k_N + ∑_{j<N} h_{b_j}` of the words read in the first `N` generations. -/
def conductorAt (N : ℕ) : ℕ := level N + ∑ j ∈ range N, hb (scale j)

/-- The defining formula of `conductorAt`. -/
theorem conductorAt_def (N : ℕ) : conductorAt N = level N + ∑ j ∈ range N, hb (scale j) := rfl

/-- **The conductor** `q_* := ⌈1668728 · (101/100)^{N_*}⌉ ∈ ℕ`, the ceiling of an exact rational
number. -/
@[collatz_pos_dens "def_qstar"]
def conductor : ℕ := ⌈(1668728 : ℚ) * (101 / 100) ^ generationThreshold⌉₊

/-- The defining formula `q_* = ⌈1668728 · (101/100)^{N_*}⌉`. -/
theorem conductor_def : conductor = ⌈(1668728 : ℚ) * (101 / 100) ^ generationThreshold⌉₊ := rfl

/- `q_*` is sealed: unfolding it lets elaboration try to evaluate `3^{q_*}` (for instance in
`ResidueGroup conductor`) and exhaust the recursion depth. Rewrite with `conductor_def` where
the value is needed. -/
attribute [irreducible] conductor

/-- The conductor is positive. -/
theorem conductor_pos : 0 < conductor := by
  rw [conductor_def]
  exact Nat.ceil_pos.2 (by positivity)

end CollatzPosDens
