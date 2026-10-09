/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Main.MainJoint

/-!
# The explicit density theorem

For every natural number `N ≥ collatzDensityThreshold = 2^2^2^2^140214`, at least
`collatzDensity · N` of the integers `n ∈ {0, …, N - 1}` reach `1` within `⌊10.46 log n⌋₊`
Collatz steps, where `collatzDensity = 1 / 2^2^2^140214`.

This is a corollary of the joint density theorem
`positive_density_collatz_and_collatzAccel_reaches_one`: the set counted there is contained in
the set counted here, since each of its elements satisfies the first conjunct, so its cardinality
is at most the cardinality here.

## Main results

* `positive_density_collatz_reaches_one`: for every `N ≥ collatzDensityThreshold`, at least
  `collatzDensity · N` of the `n < N` reach `1` within `⌊10.46 log n⌋₊` Collatz steps.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  Theorem 1.1.
-/

@[expose] public section

open Finset

/-- **The explicit density theorem**. For every `N ≥ collatzDensityThreshold`, at least
`collatzDensity · N` of the `n ∈ {0, …, N - 1}` reach `1` within `⌊10.46 log n⌋₊` Collatz steps. -/
@[collatz_pos_dens "thm_main"]
theorem positive_density_collatz_reaches_one (N : ℕ) (hN : collatzDensityThreshold ≤ N) :
    collatzDensity * N ≤ #{n ∈ range N | CollatzOneWithin n ⌊(10.46 : ℝ) * Real.log n⌋₊} :=
  (positive_density_collatz_and_collatzAccel_reaches_one N hN).trans <| by
    gcongr with n _
    exact And.left
