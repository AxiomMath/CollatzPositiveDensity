/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Main.EndpointJoint

/-!
# The explicit joint density theorem

For every natural number `N ≥ X_ch = 2 ^ 2 ^ 2 ^ 2 ^ 140214`, at least `c_ch · N` of the odd
integers `n ∈ {0, …, N - 1}` reach `1` within `⌊10.46 log n⌋₊` Collatz steps and within
`⌊3.4881 log n⌋₊` accelerated Collatz steps, where `c_ch = 1 / 2 ^ 2 ^ 2 ^ 140214`.

This is the joint density theorem for a prescribed endpoint `s` coprime to `6`
(`positive_density_collatz_and_collatzAccel_reaches_of_coprime_six`) at `s = 1`: there
`c(1) = 1 / (1 ^ 4 · 2 ^ 2 ^ 2 ^ 140214) = c_ch`, `X(1) = 2 ^ (1 ^ 3 · 2 ^ 2 ^ 2 ^ 140214) = X_ch`
and `log (n / 1) = log n`.

## Main results

* `positive_density_collatz_and_collatzAccel_reaches_one`: for `N ≥ collatzDensityThreshold`, at
  least `collatzDensity · N` of the `n < N` reach `1` within the stated Collatz and accelerated
  Collatz step bounds.

## Implementation notes

The identifications `c(1) = c_ch` and `X(1) = X_ch` are made by rewriting `1 ^ k = 1` and
`1 · a = a` in the same expressions with the innermost exponent `140214` replaced by a variable
`x`, and then specializing to `x = 140214` definitionally. Working with a variable keeps the
kernel from attempting to evaluate the towers, which it refuses to do.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset

/-- `2 ^ 2 ^ 2 ^ 2 ^ x`; `X_ch` is its value at `x = 140214`. -/
private def towerFour (x : ℕ) : ℕ := 2 ^ 2 ^ 2 ^ 2 ^ x

/-- `2 ^ (s ^ 3 · 2 ^ 2 ^ 2 ^ x)`; `X(s)` is its value at `x = 140214`. -/
private def thresholdTower (s x : ℕ) : ℕ := 2 ^ (s ^ 3 * 2 ^ 2 ^ 2 ^ x)

/-- `1 / 2 ^ 2 ^ 2 ^ x`; `c_ch` is its value at `x = 140214`. -/
private def densityTower (x : ℕ) : ℚ := 1 / 2 ^ 2 ^ 2 ^ x

/-- `1 / (s ^ 4 · 2 ^ 2 ^ 2 ^ x)`; `c(s)` is its value at `x = 140214`. -/
private def densityDepTower (s x : ℕ) : ℚ := 1 / (s ^ 4 * 2 ^ 2 ^ 2 ^ x)

private theorem thresholdTower_one (x : ℕ) : thresholdTower 1 x = towerFour x := by
  unfold thresholdTower towerFour
  rw [Nat.one_pow, Nat.one_mul]

private theorem densityDepTower_one (x : ℕ) : densityDepTower 1 x = densityTower x := by
  unfold densityDepTower densityTower
  rw [Nat.cast_one, one_pow, one_mul]

/-- `X(1) = X_ch`. -/
private theorem collatzDensityThresholdDep_one :
    collatzDensityThresholdDep 1 = collatzDensityThreshold :=
  (thresholdTower_one 140214 : thresholdTower 1 140214 = towerFour 140214)

/-- `c(1) = c_ch`. -/
private theorem collatzDensityDep_one : collatzDensityDep 1 = collatzDensity :=
  (densityDepTower_one 140214 : densityDepTower 1 140214 = densityTower 140214)

/-- **The explicit joint density theorem.** For every `N ≥ X_ch`, at least `c_ch · N` of the odd
`n ∈ {0, …, N - 1}` reach `1` within `⌊10.46 log n⌋₊` Collatz steps and within
`⌊3.4881 log n⌋₊` accelerated Collatz steps. -/
@[collatz_pos_dens "thm_main_joint"]
theorem positive_density_collatz_and_collatzAccel_reaches_one
    {N : ℕ} (hN : collatzDensityThreshold ≤ N) :
    collatzDensity * N ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz 1 n ⌊(10.46 : ℝ) * Real.log n⌋₊ ∧
      ReachWithin collatzAccel 1 n ⌊(3.4881 : ℝ) * Real.log n⌋₊} := by
  have h := positive_density_collatz_and_collatzAccel_reaches_of_coprime_six
    (Nat.coprime_one_left 6) (collatzDensityThresholdDep_one ▸ hN)
  simpa only [collatzDensityDep_one, Nat.cast_one, div_one] using h
