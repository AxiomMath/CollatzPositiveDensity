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
# Counting set of the main theorem inside the counting set of the challenge

Fix an endpoint `t`. The main theorem counts the odd integers `1 ≤ n < N` that reach `t` within
`⌊(523/50) log(n/t)⌋₊` Collatz steps and reach the odd part `t / 2^{v₂(t)}` of `t` within
`⌊(34881/10000) log(n/t)⌋₊` accelerated Collatz steps, whereas the challenge statement counts the
odd `n ∈ {0, …, N - 1}` with the same accelerated condition that reach `t` within
`⌊(1046/100) log(n/t)⌋₊` Collatz steps. Since `523/50 = 1046/100`, the first set is contained in
the second.

## Main results

* `CollatzPosDens.count_superset`: the inclusion of the two counting sets.

## Implementation notes

The left-hand set is a subset of `ℕ`, and the right-hand set is the coercion of a `Finset`
filtered from `Finset.range N`, matching the index set `{0, …, N - 1}` of the challenge. The
quotient `n / t` inside the logarithm is real division.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `t` and `N`, the odd integers `1 ≤ n < N` reaching `t` within
`⌊(523/50) log(n/t)⌋₊` Collatz steps and reaching `t / 2^{v₂(t)}` within
`⌊(34881/10000) log(n/t)⌋₊` accelerated steps form a subset of the odd `n ∈ {0, …, N - 1}` with
the same accelerated condition reaching `t` within `⌊(1046/100) log(n/t)⌋₊` Collatz steps. -/
@[collatz_pos_dens "lem_count_superset"]
theorem count_superset (t N : ℕ) :
    {n : ℕ | 1 ≤ n ∧ n < N ∧
        (Odd n ∧ ReachWithin collatz t n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊)} ⊆
      ↑{n ∈ Finset.range N | Odd n ∧
        ReachWithin collatz t n ⌊(1046 / 100 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊} := by
  rintro n ⟨-, hnN, hodd, hn, hacc⟩
  have h : (523 / 50 : ℝ) = 1046 / 100 := by norm_num
  rw [h] at hn
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
  exact ⟨hnN, hodd, hn, hacc⟩

end CollatzPosDens
