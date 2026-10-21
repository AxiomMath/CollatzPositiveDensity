/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.TowerConstant
public import CollatzPosDens.Recipe.TargetExp
public import CollatzPosDens.Main.MnInternal
public import CollatzPosDens.Main.CountSuperset

/-!
# The endpoint theorem with the tower constants

Let `D_A = 2 ^ 2 ^ 2 ^ 163` be the tower constant (`towerConstant`) and `κ_t = 25/11` the target
exponent (`targetExp`). For every natural number `t` with `3 ∤ t` and every `N`, at least
`⌊N / (t ^ κ_t D_A)⌋₊` of the odd integers `n ∈ {0, …, N - 1}` reach `t` within
`⌊(1046/100) log(n/t)⌋₊` Collatz steps and reach the odd part `t / 2^{v₂(t)}` of `t` within
`⌊(34881/10000) log(n/t)⌋₊` accelerated Collatz steps. Here `t ^ κ_t` is a real power.

The proof splits at `N = D_A t`. If `N ≥ D_A t`, the joint count
`div_rpow_mul_towerConstant_le_ncard_reach` at the real scale `X = N` gives at least
`N / (t ^ κ_t D_A)` elements, all of which lie in the counted set, and the floor is at most its
argument. If `N < D_A t`, then `N / (t ^ κ_t D_A) < t ^ {1 - κ_t} ≤ 1`, so the floor on the left
is `0`.

## Main results

* `CollatzPosDens.div_le_card_reach_of_two_pow_le`: the endpoint theorem with the tower
  constants.

## Implementation notes

The density `N / (t ^ κ_t D_A)` is real division, and its natural-number floor is compared with
the cardinality in `ℕ`. The tower constant is never evaluated: it enters only through its
positivity and the hypothesis `N ≥ D_A t`. In the case `N < D_A t` the proof uses `t ≤ t ^ κ_t`
(as `t ≥ 1` and `κ_t ≥ 1`) in place of the identity `t / t ^ κ_t = t ^ {1 - κ_t}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- **The endpoint theorem with the tower constants.** For every `t` with `3 ∤ t` and every `N`,
at least `⌊N / (t ^ κ_t D_A)⌋₊` of the odd `n ∈ {0, …, N - 1}` reach `t` within
`⌊(1046/100) log(n/t)⌋₊` Collatz steps and reach `t / 2^{v₂(t)}` within
`⌊(34881/10000) log(n/t)⌋₊` accelerated Collatz steps; here `D_A = towerConstant`,
`κ_t = targetExp` and `t ^ κ_t` is a real power. -/
@[collatz_pos_dens "thm_endpoint_tower"]
theorem div_le_card_reach_of_two_pow_le {t : ℕ} (ht : ¬ 3 ∣ t) (N : ℕ) :
    ⌊(N : ℝ) / ((t : ℝ) ^ (targetExp : ℝ) * towerConstant)⌋₊ ≤
      #{n ∈ range N | Odd n ∧
        ReachWithin collatz t n ⌊(1046 / 100 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊} := by
  have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; exact ht (dvd_zero 3))
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht0
  have hD : (0 : ℝ) < towerConstant := by exact_mod_cast towerConstant_pos
  have htκ : (t : ℝ) ≤ (t : ℝ) ^ (targetExp : ℝ) := by
    calc (t : ℝ) = (t : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (t : ℝ) ^ (targetExp : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le htR (by rw [targetExp_cast]; norm_num)
  have hd : (0 : ℝ) < (t : ℝ) ^ (targetExp : ℝ) * towerConstant := by
    have : (0 : ℝ) < (t : ℝ) ^ (targetExp : ℝ) := by linarith
    positivity
  rcases lt_or_ge N (towerConstant * t) with hN | hN
  · refine (Nat.floor_eq_zero.2 ?_).trans_le (Nat.zero_le _)
    rw [div_lt_one hd]
    have hN' : (N : ℝ) < towerConstant * t := by exact_mod_cast hN
    calc (N : ℝ) < towerConstant * t := hN'
      _ ≤ towerConstant * (t : ℝ) ^ (targetExp : ℝ) := mul_le_mul_of_nonneg_left htκ hD.le
      _ = _ := mul_comm _ _
  have hM := div_rpow_mul_towerConstant_le_ncard_reach ht (X := N) (by exact_mod_cast hN)
  have hle : ({n : ℕ | 1 ≤ n ∧ (n : ℝ) < N ∧
        (Odd n ∧ ReachWithin collatz t n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊)}.ncard : ℝ) ≤
      (#{n ∈ range N | Odd n ∧
        ReachWithin collatz t n ⌊(1046 / 100 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
          ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊} : ℝ) := by
    rw [← Set.ncard_coe_finset]
    refine Nat.cast_le.2 (Set.ncard_le_ncard (fun n hn => count_superset t N ?_)
      (Finset.finite_toSet _))
    obtain ⟨h1, hn, h2⟩ := hn
    exact ⟨h1, by exact_mod_cast hn, h2⟩
  exact Nat.floor_le_of_le (hM.trans hle)

end CollatzPosDens
