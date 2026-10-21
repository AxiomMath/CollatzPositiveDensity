/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.TowerConstant
public import CollatzPosDens.Recipe.PhEndpointDensityLe
public import CollatzPosDens.Main.EndpointTower

/-!
# The joint density theorem for an endpoint prime to three

Let `t` be a natural number not divisible by `3`, let `D_A = 2 ^ 2 ^ 2 ^ 163` (`towerConstant`)
and `c_end(t) = 1 / (t ^ (25/11) · D_A)` (`collatzDensityDep`). For every `N`, at least
`⌊c_end(t) · N⌋₊` of the odd integers `n ∈ {0, …, N - 1}` reach `t` within `⌊10.46 log (n / t)⌋₊`
Collatz steps and reach the odd part `t / 2 ^ v₂(t)` of `t` within `⌊3.4881 log (n / t)⌋₊`
accelerated Collatz steps. The power of `t` is a real power.

The result follows from `div_le_card_reach_of_two_pow_le`, which gives the same bound with
`⌊N / (t ^ κ · D_A)⌋₊` in place of `⌊c_end(t) · N⌋₊`, where `κ = targetExp`. Since
`c_end(t) ≤ 1 / (t ^ κ · D_A)` (`collatzDensityDep_le`), monotonicity of the floor gives
`⌊c_end(t) · N⌋₊ ≤ ⌊N / (t ^ κ · D_A)⌋₊`.

## Main results

* `positive_density_collatz_and_collatzAccel_reaches_of_not_three_dvd`: the joint density
  theorem for an endpoint prime to three.

## Implementation notes

The decimal literals `10.46` and `3.4881` are the rationals `1046 / 100` and `34881 / 10000`.
The tower constant `towerConstant` is never evaluated: it enters only through comparisons.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset CollatzPosDens

/-- For `t` not divisible by `3` and every `N`, at least `⌊collatzDensityDep t · N⌋₊` of the odd
`n < N` reach `t` within `⌊10.46 log (n / t)⌋₊` Collatz steps and reach the odd part of `t` within
`⌊3.4881 log (n / t)⌋₊` accelerated Collatz steps. -/
@[collatz_pos_dens "thm_endpoint_not_three_dvd"]
theorem positive_density_collatz_and_collatzAccel_reaches_of_not_three_dvd
    {t : ℕ} (ht : ¬3 ∣ t) (N : ℕ) :
    ⌊collatzDensityDep t * N⌋₊ ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz t n ⌊(10.46 : ℝ) * Real.log (n / t)⌋₊ ∧
      ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n ⌊(3.4881 : ℝ) * Real.log (n / t)⌋₊} := by
  have h1 : (10.46 : ℝ) = 1046 / 100 := by norm_num
  have h2 : (3.4881 : ℝ) = 34881 / 10000 := by norm_num
  rw [h1, h2]
  refine le_trans (Nat.floor_le_floor ?_) (div_le_card_reach_of_two_pow_le ht N)
  refine (mul_le_mul_of_nonneg_right (collatzDensityDep_le t) (Nat.cast_nonneg N)).trans ?_
  rw [one_div_mul_eq_div]
