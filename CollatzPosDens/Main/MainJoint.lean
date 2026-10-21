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

For every natural number `N`, at least `⌊c_ch · N⌋₊` of the odd integers `n ∈ {0, …, N - 1}`
reach `1` within `⌊10.46 log n⌋₊` Collatz steps and within `⌊3.4881 log n⌋₊` accelerated Collatz
steps, where `c_ch = 1 / 2 ^ 2 ^ 2 ^ 163` (`collatzDensity`).

This is the joint density theorem for a prescribed endpoint `t` coprime to `6`
(`positive_density_collatz_and_collatzAccel_reaches_of_coprime_six`) at `t = 1`: since the real
power `1 ^ (25/11)` equals `1`, there `c_end(1) = 1 / (1 ^ (25/11) · 2 ^ 2 ^ 2 ^ 163)` is the
real image of `c_ch`, and `log (n / 1) = log n`. The natural-number floor of a rational number
equals that of its real image.

## Main results

* `positive_density_collatz_and_collatzAccel_reaches_one`: the challenge statement.

## Implementation notes

The identification of `c_end(1)` with the real image of `c_ch` is proved for auxiliary
definitions with the innermost exponent `163` replaced by a variable `x`, and then specialized to
`x = 163` definitionally. Comparing two definitions applied to `163` lets the kernel match them
argument by argument, so it never attempts to evaluate a tower.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset

/-- `1 / 2 ^ 2 ^ 2 ^ x`; `c_ch` is its value at `x = 163`. -/
private def densityTower (x : ℕ) : ℚ := 1 / 2 ^ 2 ^ 2 ^ x

/-- `1 / (t ^ (25/11) · 2 ^ 2 ^ 2 ^ x)`; `c_end(t)` is its value at `x = 163`. -/
private noncomputable def densityDepTower (t x : ℕ) : ℝ :=
  1 / (t ^ (25 / 11 : ℝ) * 2 ^ 2 ^ 2 ^ x)

private theorem densityDepTower_one (x : ℕ) :
    densityDepTower 1 x = (densityTower x : ℝ) := by
  unfold densityDepTower densityTower
  rw [Nat.cast_one, Real.one_rpow, one_mul, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_ofNat]

/-- `c_end(1)` is the real image of `c_ch`. -/
private theorem collatzDensityDep_one : collatzDensityDep 1 = (collatzDensity : ℝ) :=
  (densityDepTower_one 163 : densityDepTower 1 163 = (densityTower 163 : ℝ))

/-- The natural-number floor of a rational number equals that of its real image. -/
private theorem natFloor_ratCast_real (q : ℚ) : ⌊(q : ℝ)⌋₊ = ⌊q⌋₊ := by
  rw [← Int.floor_toNat, ← Int.floor_toNat, Rat.floor_cast]

/-- **The explicit density theorem**, both clocks at once: for every `N`, at least `⌊c N⌋` of
odd starting values `n < N` reach `1` in at most `⌊10.46 log n⌋` Collatz steps and
in at most `⌊3.4881 log n⌋` accelerated Collatz steps. -/
@[collatz_pos_dens "thm_main_joint"]
theorem positive_density_collatz_and_collatzAccel_reaches_one (N : ℕ) :
    ⌊collatzDensity * N⌋₊ ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz 1 n ⌊(10.46 : ℝ) * Real.log n⌋₊ ∧
      ReachWithin collatzAccel 1 n ⌊(3.4881 : ℝ) * Real.log n⌋₊} := by
  have h := positive_density_collatz_and_collatzAccel_reaches_of_coprime_six
    (Nat.coprime_one_left 6) N
  simp only [Nat.cast_one, div_one] at h
  rw [collatzDensityDep_one] at h
  rw [← natFloor_ratCast_real, Rat.cast_mul, Rat.cast_natCast]
  exact h
