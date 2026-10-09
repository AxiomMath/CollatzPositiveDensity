module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves.

-/

@[expose] public section

open Finset

/-- The Collatz map: `n ↦ n / 2` for even `n`, and `n ↦ 3n + 1` for odd `n`. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` reaches `1` in at most `steps` applications of the Collatz map. -/
@[reducible]
def CollatzOneWithin (n steps : ℕ) : Prop :=
  ∃ r ≤ steps, collatz^[r] n = 1

/-- The density constant `c = 1 / 2^2^2^140214`. -/
def collatzDensity : ℚ :=
  1 / 2 ^ 2 ^ 2 ^ 140214

/-- The cutoff `X₀ = 2^2^2^2^140214`. -/
def collatzDensityThreshold : ℕ :=
  2 ^ 2 ^ 2 ^ 2 ^ 140214

/-- **The explicit density theorem**, ordinary clock: for every `N ≥ X₀`, at least `c N` of the
`n < N` reach `1` in at most `⌊10.46 log n⌋` Collatz steps. A direct corollary of the joint theorem
below. -/
theorem positive_density_collatz_reaches_one (N : ℕ) (hN : collatzDensityThreshold ≤ N) :
    collatzDensity * N ≤ #{n ∈ range N | CollatzOneWithin n ⌊(10.46 : ℝ) * Real.log n⌋₊} :=
  sorry

/-- Accelerated Collatz map, aka Syracuse map. Sends odd `n` to `3n + 1` divided by the highest
power of 2 that divides `3n + 1`. -/
def collatzAccel (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

/-- The odd part `n / 2 ^ padicValNat 2 n` of `n` reaches `1` in at most `steps` applications of
the accelerated Collatz map (which fixes `1`). -/
@[reducible]
def CollatzAccelOneWithin (n steps : ℕ) : Prop :=
  collatzAccel^[steps] (n / 2 ^ padicValNat 2 n) = 1

/-- **The explicit density theorem**, both clocks at once: for every `N ≥ X₀`, at least `c N` of
the `n < N` reach `1` in at most `⌊10.46 log n⌋` Collatz steps and, starting from their odd part,
in at most `⌊3.4881 log n⌋` accelerated Collatz steps. -/
theorem positive_density_collatz_and_collatzAccel_reaches_one
    (N : ℕ) (hN : collatzDensityThreshold ≤ N) :
    collatzDensity * N ≤
    #{n ∈ range N | CollatzOneWithin n ⌊(10.46 : ℝ) * Real.log n⌋₊ ∧
      CollatzAccelOneWithin n ⌊(3.4881 : ℝ) * Real.log n⌋₊} :=
  sorry
