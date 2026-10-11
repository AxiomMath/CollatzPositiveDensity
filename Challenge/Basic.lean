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

/-- The orbit of `f` starting from `n` reaches target within `steps` steps. -/
@[reducible]
def ReachWithin {α : Type*} (f : α → α) (target n : α) (steps : ℕ) : Prop :=
  ∃ r ≤ steps, f^[r] n = target

/-- The density constant `c = 1 / 2^2^2^140214`. -/
def collatzDensity : ℚ :=
  1 / 2 ^ 2 ^ 2 ^ 140214

/-- The cutoff `X₀ = 2^2^2^2^140214`. -/
def collatzDensityThreshold : ℕ :=
  2 ^ 2 ^ 2 ^ 2 ^ 140214

/-- **The explicit density theorem**, ordinary clock: for every `N ≥ X₀`, at least `c N` of the
`n < N` reach `1` in at most `⌊10.46 log n⌋` Collatz steps. A direct corollary of the joint theorem
below. -/
theorem positive_density_collatz_reaches_one {N : ℕ} (hN : collatzDensityThreshold ≤ N) :
    collatzDensity * N ≤ #{n ∈ range N | ReachWithin collatz 1 n ⌊(10.46 : ℝ) * Real.log n⌋₊} :=
  sorry

section with_accel

/-- Accelerated Collatz map, aka Syracuse map. Sends odd `n` to `3n + 1` divided by the highest
power of 2 that divides `3n + 1`. -/
def collatzAccel (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

/-- **The explicit density theorem**, both clocks at once: for every `N ≥ X₀`, at least `c N` of
odd starting values `n < N` reach `1` in at most `⌊10.46 log n⌋` Collatz steps and
in at most `⌊3.4881 log n⌋` accelerated Collatz steps. -/
theorem positive_density_collatz_and_collatzAccel_reaches_one
    {N : ℕ} (hN : collatzDensityThreshold ≤ N) :
    collatzDensity * N ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz 1 n ⌊(10.46 : ℝ) * Real.log n⌋₊ ∧
      ReachWithin collatzAccel 1 n ⌊(3.4881 : ℝ) * Real.log n⌋₊} :=
  sorry

end with_accel

section generalized

/-- The density constant `c = 1 / (s^4 * 2^2^2^140214)`. -/
def collatzDensityDep (s : ℕ) : ℚ :=
  1 / (s ^ 4 * 2 ^ 2 ^ 2 ^ 140214)

/-- The cutoff `X₀ = 2^(s^3 * 2^2^2^140214)`. -/
def collatzDensityThresholdDep (s : ℕ) : ℕ :=
  2 ^ (s ^ 3 * 2 ^ 2 ^ 2 ^ 140214)

/-- **The generalized explicit density theorem**, both clocks at once:
for any `s` coprime to `6`, for every `N ≥ X₀(s)`, at least `c(s) N` of odd starting values `n < N`
reach `s` in at most `⌊10.46 log (n/s)⌋` Collatz steps and
in at most `⌊3.4881 log (n/s)⌋` accelerated Collatz steps. -/
theorem positive_density_collatz_and_collatzAccel_reaches_of_coprime_six
    {s : ℕ} (hs : s.Coprime 6) {N : ℕ} (hN : collatzDensityThresholdDep s ≤ N) :
    collatzDensityDep s * N ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz s n ⌊(10.46 : ℝ) * Real.log (n / s)⌋₊ ∧
      ReachWithin collatzAccel s n ⌊(3.4881 : ℝ) * Real.log (n / s)⌋₊} :=
  sorry

end generalized
