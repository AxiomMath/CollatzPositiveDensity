/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.X0
public import CollatzPosDens.Recipe.CM
public import CollatzPosDens.Recipe.X0Tower
public import CollatzPosDens.Recipe.InvcTower
public import CollatzPosDens.Main.CountSuperset
public import CollatzPosDens.Main.MnInternal

/-!
# The joint density theorem for a prescribed endpoint coprime to six

Let `s` be a natural number coprime to `6`. For every natural number `N ≥ X(s)`, where
`X(s) = 2 ^ (s ^ 3 · 2 ^ 2 ^ 2 ^ 140214)`, at least `c(s) · N` of the odd integers
`n ∈ {0, …, N - 1}` reach `s` within `⌊10.46 log (n / s)⌋₊` Collatz steps and within
`⌊3.4881 log (n / s)⌋₊` accelerated Collatz steps, where `c(s) = 1 / (s ^ 4 · 2 ^ 2 ^ 2 ^ 140214)`.

Coprimality to `6` makes `s` positive, odd and prime to `3`. The proof applies the internal joint
count `c_M(s) X ≤ #{…}` at `X = N` (valid since `X_0(s) < X(s) ≤ N`), enlarges the counted set to
the challenge's, and replaces `c_M(s)` by the smaller `c(s)`.

## Main results

* `positive_density_collatz_and_collatzAccel_reaches_of_coprime_six`: the challenge statement.

## Implementation notes

The challenge states the inequality in `ℚ`; it is proved in `ℝ` and transported back, since the
inclusion `ℚ → ℝ` preserves and reflects order. The towers in `X(s)` and `c(s)` are only ever
compared symbolically, never evaluated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset CollatzPosDens

/-- **The joint density theorem for an endpoint coprime to six.** For `s` coprime to `6` and
every `N ≥ X(s)`, at least `c(s) · N` of the odd `n ∈ {0, …, N - 1}` reach `s` within
`⌊10.46 log (n / s)⌋₊` Collatz steps and within `⌊3.4881 log (n / s)⌋₊` accelerated Collatz
steps. -/
@[collatz_pos_dens "thm_endpoint_joint"]
theorem positive_density_collatz_and_collatzAccel_reaches_of_coprime_six
    {s : ℕ} (hs : s.Coprime 6) {N : ℕ} (hN : collatzDensityThresholdDep s ≤ N) :
    collatzDensityDep s * N ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz s n ⌊(10.46 : ℝ) * Real.log (n / s)⌋₊ ∧
      ReachWithin collatzAccel s n ⌊(3.4881 : ℝ) * Real.log (n / s)⌋₊} := by
  -- `s` is positive, odd and prime to `3`
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · simp at hs
    · exact h
  have hso : Odd s := by
    rcases Nat.even_or_odd s with h | h
    · have h2 : (2 : ℕ) ∣ s.gcd 6 := Nat.dvd_gcd (even_iff_two_dvd.1 h) (by norm_num)
      rw [hs] at h2
      norm_num at h2
    · exact h
  have hs3 : ¬ 3 ∣ s := by
    intro h
    have h3 : (3 : ℕ) ∣ s.gcd 6 := Nat.dvd_gcd h (by norm_num)
    rw [hs] at h3
    norm_num at h3
  have h1 : (10.46 : ℝ) = 1046 / 100 := by norm_num
  have h2 : (3.4881 : ℝ) = 34881 / 10000 := by norm_num
  rw [h1, h2]
  set c := #{n ∈ range N | Odd n ∧
      ReachWithin collatz s n ⌊(1046 / 100 : ℝ) * Real.log ((n : ℝ) / s)⌋₊ ∧
      ReachWithin collatzAccel s n ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / s)⌋₊} with hc
  -- `X_0(s) ≤ N`
  have hcut : cutoff s ≤ N := (cutoff_lt_collatzDensityThresholdDep hs0).le.trans hN
  have hM := densityConst_mul_le_ncard_reach hs0 hso hs3 (X := (N : ℝ)) (by exact_mod_cast hcut)
  -- the internal set sits inside the challenge's
  have hsub := count_superset s N
  have hle : {n : ℕ | 1 ≤ n ∧ (n : ℝ) < N ∧
        (Odd n ∧ ReachWithin collatz s n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / s)⌋₊ ∧
          ReachWithin collatzAccel s n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / s)⌋₊)}.ncard ≤ c := by
    rw [hc, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    intro n hn
    refine hsub ⟨hn.1, ?_, hn.2.2⟩
    exact_mod_cast hn.2.1
  have hMc : densityConst s * N ≤ (c : ℝ) := hM.trans (by exact_mod_cast hle)
  -- `c(s) ≤ c_M(s)`
  have hcd : ((collatzDensityDep s : ℚ) : ℝ) ≤ densityConst s :=
    (collatzDensityDep_lt_densityConst hs0).le
  have hR : ((collatzDensityDep s : ℚ) : ℝ) * N ≤ (c : ℝ) :=
    (mul_le_mul_of_nonneg_right hcd (Nat.cast_nonneg N)).trans hMc
  exact_mod_cast hR
