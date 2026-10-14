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

Let `t` be a natural number coprime to `6`. For every natural number `N ≥ X(t)`, where
`X(t) = 2 ^ (t ^ 3 · 2 ^ 2 ^ 2 ^ 87640)`, at least `c(t) · N` of the odd integers
`n ∈ {0, …, N - 1}` reach `t` within `⌊10.46 log (n / t)⌋₊` Collatz steps and within
`⌊3.4881 log (n / t)⌋₊` accelerated Collatz steps, where `c(t) = 1 / (t ^ 4 · 2 ^ 2 ^ 2 ^ 87640)`.

Coprimality to `6` makes `t` positive, odd and prime to `3`. The proof applies the internal joint
count `c_M(t) X ≤ #{…}` at `X = N` (valid since `X_0(t) < X(t) ≤ N`), enlarges the counted set to
the challenge's, and replaces `c_M(t)` by the smaller `c(t)`.

## Main results

* `positive_density_collatz_and_collatzAccel_reaches_of_coprime_six`: the challenge statement.

## Implementation notes

The challenge states the inequality in `ℚ`; it is proved in `ℝ` and transported back, since the
inclusion `ℚ → ℝ` preserves and reflects order. The towers in `X(t)` and `c(t)` are only ever
compared symbolically, never evaluated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset CollatzPosDens

/-- **The joint density theorem for an endpoint coprime to six.** For `t` coprime to `6` and
every `N ≥ X(t)`, at least `c(t) · N` of the odd `n ∈ {0, …, N - 1}` reach `t` within
`⌊10.46 log (n / t)⌋₊` Collatz steps and within `⌊3.4881 log (n / t)⌋₊` accelerated Collatz
steps. -/
@[collatz_pos_dens "thm_endpoint_joint"]
theorem positive_density_collatz_and_collatzAccel_reaches_of_coprime_six
    {t : ℕ} (ht : t.Coprime 6) {N : ℕ} (hN : collatzDensityThresholdDep t ≤ N) :
    collatzDensityDep t * N ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz t n ⌊(10.46 : ℝ) * Real.log (n / t)⌋₊ ∧
      ReachWithin collatzAccel t n ⌊(3.4881 : ℝ) * Real.log (n / t)⌋₊} := by
  -- `t` is positive, odd and prime to `3`
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at ht
    · exact h
  have hto : Odd t := by
    rcases Nat.even_or_odd t with h | h
    · have h2 : (2 : ℕ) ∣ t.gcd 6 := Nat.dvd_gcd (even_iff_two_dvd.1 h) (by norm_num)
      rw [ht] at h2
      norm_num at h2
    · exact h
  have ht3 : ¬ 3 ∣ t := by
    intro h
    have h3 : (3 : ℕ) ∣ t.gcd 6 := Nat.dvd_gcd h (by norm_num)
    rw [ht] at h3
    norm_num at h3
  have h1 : (10.46 : ℝ) = 1046 / 100 := by norm_num
  have h2 : (3.4881 : ℝ) = 34881 / 10000 := by norm_num
  rw [h1, h2]
  set c := #{n ∈ range N | Odd n ∧
      ReachWithin collatz t n ⌊(1046 / 100 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
      ReachWithin collatzAccel t n ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊} with hc
  -- `X_0(t) ≤ N`
  have hcut : cutoff t ≤ N := (cutoff_lt_collatzDensityThresholdDep ht0).le.trans hN
  have hM := densityConst_mul_le_ncard_reach ht0 hto ht3 (X := (N : ℝ)) (by exact_mod_cast hcut)
  -- the internal set sits inside the challenge's
  have hsub := count_superset t N
  have hle : {n : ℕ | 1 ≤ n ∧ (n : ℝ) < N ∧
        (Odd n ∧ ReachWithin collatz t n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel t n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊)}.ncard ≤ c := by
    rw [hc, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    intro n hn
    refine hsub ⟨hn.1, ?_, hn.2.2⟩
    exact_mod_cast hn.2.1
  have hMc : densityConst t * N ≤ (c : ℝ) := hM.trans (by exact_mod_cast hle)
  -- `c(t) ≤ c_M(t)`
  have hcd : ((collatzDensityDep t : ℚ) : ℝ) ≤ densityConst t :=
    (collatzDensityDep_lt_densityConst ht0).le
  have hR : ((collatzDensityDep t : ℚ) : ℝ) * N ≤ (c : ℝ) :=
    (mul_le_mul_of_nonneg_right hcd (Nat.cast_nonneg N)).trans hMc
  exact_mod_cast hR
