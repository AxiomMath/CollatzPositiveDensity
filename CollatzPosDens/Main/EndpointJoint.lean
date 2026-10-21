/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Main.EndpointNotThreeDvd

/-!
# The joint density theorem for a prescribed endpoint coprime to six

Let `t` be a natural number coprime to `6`, and let `D_A = 2 ^ 2 ^ 2 ^ 163` be the tower
constant. For every `N`, at least `⌊c_end(t) · N⌋₊` of the odd integers `n ∈ {0, …, N - 1}`
reach `t` within `⌊10.46 log (n / t)⌋₊` Collatz steps and within `⌊3.4881 log (n / t)⌋₊`
accelerated Collatz steps, where `c_end(t) = 1 / (t ^ (25/11) · D_A)` (`collatzDensityDep`).
The power of `t` is a real power, and the comparison is in `ℕ`.

Coprimality to `6` makes `t` odd and prime to `3`. Being prime to `3`, the joint density theorem
for an endpoint prime to three applies; being odd, `t` is its own odd part `t / 2 ^ v₂(t) = t`,
so the set counted there is the set counted here.

## Main results

* `positive_density_collatz_and_collatzAccel_reaches_of_coprime_six`: the joint density theorem
  for an endpoint coprime to six.

## Implementation notes

The statement is verbatim the challenge statement: the hypothesis `t.Coprime 6` is
`gcd(t, 6) = 1`, and the decimal literals `10.46` and `3.4881` are the rationals `1046 / 100`
and `34881 / 10000`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset CollatzPosDens

/-- **The generalized explicit density theorem**, both clocks at once:
for any `t` coprime to `6`, for every `N`, at least `⌊c(t) N⌋` of odd starting values `n < N`
reach `t` in at most `⌊10.46 log (n/t)⌋` Collatz steps and
in at most `⌊3.4881 log (n/t)⌋` accelerated Collatz steps. -/
@[collatz_pos_dens "thm_endpoint_joint"]
theorem positive_density_collatz_and_collatzAccel_reaches_of_coprime_six
    {t : ℕ} (ht : t.Coprime 6) (N : ℕ) :
    ⌊collatzDensityDep t * N⌋₊ ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz t n ⌊(10.46 : ℝ) * Real.log (n / t)⌋₊ ∧
      ReachWithin collatzAccel t n ⌊(3.4881 : ℝ) * Real.log (n / t)⌋₊} := by
  have ht3 : ¬ 3 ∣ t := fun h =>
    absurd (Nat.dvd_gcd h (by norm_num : 3 ∣ 6)) (by rw [ht]; norm_num)
  have ht2 : ¬ 2 ∣ t := fun h =>
    absurd (Nat.dvd_gcd h (by norm_num : 2 ∣ 6)) (by rw [ht]; norm_num)
  have hodd : t / 2 ^ padicValNat 2 t = t := by
    rw [padicValNat.eq_zero_of_not_dvd ht2, pow_zero, Nat.div_one]
  have h := positive_density_collatz_and_collatzAccel_reaches_of_not_three_dvd ht3 N
  rwa [hodd] at h
