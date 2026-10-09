/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Range
public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions

/-!
# Inclusion of two sets of fast-converging integers

For `N : ℕ`, the set of integers `1 ≤ n < N` that reach `1` within `⌊(523/50) log n⌋₊` Collatz
steps and within `⌊(34881/10000) log n⌋₊` accelerated Collatz steps is contained in the set of
`n ∈ {0, …, N - 1}` that reach `1` within `⌊(1046/100) log n⌋₊` Collatz steps and within
`⌊(34881/10000) log n⌋₊` accelerated Collatz steps, since `523/50 = 1046/100`.

## Main results

* `CollatzPosDens.count_superset`: the inclusion of these two sets.

## Implementation notes

The first set is a subset of `ℕ`, and the second is the coercion of a `Finset` filtered from
`Finset.range N`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `N`, the integers `1 ≤ n < N` reaching `1` within `⌊(523/50) log n⌋₊` Collatz
steps and within `⌊(34881/10000) log n⌋₊` accelerated steps form a subset of the
`n ∈ {0, …, N - 1}` reaching `1` within `⌊(1046/100) log n⌋₊` Collatz steps and within
`⌊(34881/10000) log n⌋₊` accelerated steps. -/
@[collatz_pos_dens "lem_count_superset"]
theorem count_superset (N : ℕ) :
    {n : ℕ | 1 ≤ n ∧ n < N ∧
        (CollatzOneWithin n ⌊(523 / 50 : ℝ) * Real.log n⌋₊ ∧
          CollatzAccelOneWithin n ⌊(34881 / 10000 : ℝ) * Real.log n⌋₊)} ⊆
      ↑{n ∈ Finset.range N |
        CollatzOneWithin n ⌊(1046 / 100 : ℝ) * Real.log n⌋₊ ∧
          CollatzAccelOneWithin n ⌊(34881 / 10000 : ℝ) * Real.log n⌋₊} := by
  rintro n ⟨-, hnN, hn, hacc⟩
  have h : (523 / 50 : ℝ) = 1046 / 100 := by norm_num
  rw [h] at hn
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
  exact ⟨hnN, hn, hacc⟩

end CollatzPosDens
