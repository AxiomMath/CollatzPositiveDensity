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
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Recipe.BhtLe
public import CollatzPosDens.Recipe.PhSeedTower
public import CollatzPosDens.Recipe.InvcTower
public import CollatzPosDens.Main.MnInternal
public import CollatzPosDens.Maps.CollatzOfInverse

/-!
# The joint density theorem for an endpoint prime to three

Let `t` be a natural number not divisible by `3`, and write `t = 2 ^ k u` with `u` odd. For every
`N ≥ X(t)`, where `X(t) = 2 ^ (t ^ 3 · 2 ^ 2 ^ 2 ^ 87640)`, at least `c(t) · N` of the odd
integers `n ∈ {0, …, N - 1}` reach `t` within `⌊10.46 log (n / t)⌋₊` Collatz steps and reach `u`
within `⌊3.4881 log (n / t)⌋₊` accelerated Collatz steps, where
`c(t) = 1 / (t ^ 4 · 2 ^ 2 ^ 2 ^ 87640)`.

The proof reduces to an odd endpoint. Choose `3 ≤ d ≤ 8` with `2 ^ d t ≡ 4` or `7 (mod 9)`; such
a `d` exists because `2` generates `(ℤ / 9ℤ)ˣ`. Then `m = (2 ^ d t - 1) / 3` is a natural number,
odd and prime to `3`, with `3 m + 1 = 2 ^ d t`. A Collatz orbit through `m` continues
`m ↦ 2 ^ d t ↦ ⋯ ↦ t` in `1 + d` further steps, and an accelerated orbit through `m` continues
`m ↦ u` in one step. Since `4 m ≥ 2 ^ d t`, we have `log (m / t) ≥ (d - 2) log 2`, which pays
for those extra steps in both clocks. The internal joint count at the endpoint `m` then gives the
claim, the endpoint changing from `t` to `m ≤ 2 ^ 8 t` costing a factor absorbed by the slack in
the seed tower bound: `2 ^ 65 𝓜(1) ^ 4 < 2 ^ 2 ^ 2 ^ 87640`.

## Main results

* `CollatzPosDens.two_pow_sixtyFive_mul_seedBound_one_pow_lt`: `2^65 𝓜(1)^4 < 2^2^2^87640`.
* `CollatzPosDens.collatzDensityDep_lt_densityConst_of_le`: `c(t) < c_M(m)` for `0 < m ≤ 2^8 t`.
* `CollatzPosDens.cutoff_lt_collatzDensityThresholdDep_of_le`: `X_0(m) < X(t)` for
  `0 < m ≤ 2^8 t`.
* `positive_density_collatz_and_collatzAccel_reaches_of_not_three_dvd`: the challenge statement.
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- The seed tower bound with room to spare, for a symbolic exponent: if `q_* < 3 · 2^t`, then
`2^65 𝓜(1)^4 < 2^2^2^(t + 3)`. -/
theorem two_pow_sixtyFive_mul_seedBound_one_pow_lt_of_conductor_lt {t : ℕ}
    (hq : conductor < 3 * 2 ^ t) : 2 ^ 65 * seedBound 1 ^ 4 < 2 ^ 2 ^ 2 ^ (t + 3) := by
  have hq3 : 3 ≤ conductor := by
    have := nine_mul_generationThreshold_le_conductor
    have := generationThreshold_eq
    omega
  have hexp : 2 ^ 65 * seedBound 1 ^ 4 = 2 ^ (217 + 16 * 3 ^ conductor) := by
    rw [seedBound_eq_two_pow, one_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have h27 : 3 ^ 3 ≤ 3 ^ conductor := Nat.pow_le_pow_right (by norm_num) hq3
  have hY1 : 217 + 16 * 3 ^ conductor < 32 * 3 ^ conductor := by norm_num at h27; omega
  have hY2 : 32 * 3 ^ conductor < 2 ^ (5 + 2 * conductor) := by
    have h34 : 3 ^ conductor < 4 ^ conductor :=
      Nat.pow_lt_pow_left (by norm_num) (by omega)
    rw [pow_add, pow_mul]
    norm_num
    omega
  have hY3 : 5 + 2 * conductor < 2 ^ (t + 3) := by
    have hone : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    rw [pow_add]
    generalize 2 ^ t = P at hq hone ⊢
    omega
  have hY : 217 + 16 * 3 ^ conductor < 2 ^ 2 ^ (t + 3) :=
    hY1.trans (hY2.trans (Nat.pow_lt_pow_right (by norm_num) hY3))
  rw [hexp]
  exact Nat.pow_lt_pow_right (by norm_num) hY

/-- The seed tower bound with room to spare: `2^65 𝓜(1)^4 < 2^2^2^87640`. -/
@[collatz_pos_dens "lem_seed_tower_slack"]
theorem two_pow_sixtyFive_mul_seedBound_one_pow_lt :
    2 ^ 65 * seedBound 1 ^ 4 < 2 ^ 2 ^ 2 ^ 87640 := by
  have h := two_pow_sixtyFive_mul_seedBound_one_pow_lt_of_conductor_lt
    conductor_lt_three_mul_two_pow
  rwa [show 87637 + 3 = 87640 from rfl] at h

/-- `c_M(s)⁻¹ < s^4 · 2^33 𝓜(1)^4` for every `s ≥ 1`. -/
theorem inv_densityConst_lt_mul_seedBound_one {s : ℕ} (hs : 0 < s) :
    (densityConst s)⁻¹ < (s : ℝ) ^ 4 * ((2 ^ 33 * seedBound 1 ^ 4 : ℕ) : ℝ) := by
  have hM1 : (1 : ℝ) ≤ seedBound s := by exact_mod_cast one_le_seedBound hs
  have hm0 : (0 : ℝ) ≤ modulusExponent s := Nat.cast_nonneg _
  have hmM : (modulusExponent s : ℝ) < seedBound s := by
    exact_mod_cast modulusExponent_lt_seedBound hs
  have hpow : (modulusExponent s : ℝ) ^ (4097 / 2048 : ℝ) < (seedBound s : ℝ) ^ 3 := by
    calc (modulusExponent s : ℝ) ^ (4097 / 2048 : ℝ)
        < (seedBound s : ℝ) ^ (4097 / 2048 : ℝ) :=
          Real.rpow_lt_rpow hm0 hmM (by norm_num)
      _ ≤ (seedBound s : ℝ) ^ ((3 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
      _ = (seedBound s : ℝ) ^ 3 := Real.rpow_natCast _ 3
  rw [inv_densityConst]
  calc 2 ^ 33 * (seedBound s : ℝ) * (modulusExponent s : ℝ) ^ (4097 / 2048 : ℝ)
      < 2 ^ 33 * (seedBound s : ℝ) * (seedBound s : ℝ) ^ 3 := by
        gcongr
    _ = (s : ℝ) ^ 4 * ((2 ^ 33 * seedBound 1 ^ 4 : ℕ) : ℝ) := by
        rw [seedBound_eq_mul s]
        push_cast
        ring

/-- For `0 < t` and `0 < m ≤ 2^8 t`, the stated density `c(t)` is below the construction's
density constant `c_M(m)`, compared in `ℝ`. -/
@[collatz_pos_dens "lem_invc_shift"]
theorem collatzDensityDep_lt_densityConst_of_le {t m : ℕ} (ht : 0 < t) (hm : 0 < m)
    (hmt : m ≤ 2 ^ 8 * t) : ((collatzDensityDep t : ℚ) : ℝ) < densityConst m := by
  have hcast : ((collatzDensityDep t : ℚ) : ℝ) =
      ((t : ℝ) ^ 4 * ((2 ^ 2 ^ 2 ^ 87640 : ℕ) : ℝ))⁻¹ := by
    simp only [collatzDensityDep, one_div, Rat.cast_inv, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have h := inv_densityConst_lt_mul_seedBound_one hm
  have hc := densityConst_pos hm
  have hT : ((2 ^ 65 * seedBound 1 ^ 4 : ℕ) : ℝ) < ((2 ^ 2 ^ 2 ^ 87640 : ℕ) : ℝ) :=
    Nat.cast_lt.2 two_pow_sixtyFive_mul_seedBound_one_pow_lt
  have hmt' : (m : ℝ) ≤ 2 ^ 8 * t := by exact_mod_cast hmt
  rw [hcast, ← inv_inv (densityConst m)]
  refine (inv_lt_inv₀ (by positivity) (inv_pos.2 hc)).2 ?_
  generalize ((2 ^ 2 ^ 2 ^ 87640 : ℕ) : ℝ) = T at hT ⊢
  calc (densityConst m)⁻¹ < (m : ℝ) ^ 4 * ((2 ^ 33 * seedBound 1 ^ 4 : ℕ) : ℝ) := h
    _ ≤ (2 ^ 8 * t : ℝ) ^ 4 * ((2 ^ 33 * seedBound 1 ^ 4 : ℕ) : ℝ) := by gcongr
    _ = (t : ℝ) ^ 4 * ((2 ^ 65 * seedBound 1 ^ 4 : ℕ) : ℝ) := by push_cast; ring
    _ < (t : ℝ) ^ 4 * T := mul_lt_mul_of_pos_left hT (by positivity)

/-- For `0 < t` and `0 < m ≤ 2^8 t`, the cutoff at the endpoint `m` is smaller than the endpoint
threshold at `t`, `X_0(m) < X(t)`. -/
@[collatz_pos_dens "lem_X0_shift"]
theorem cutoff_lt_collatzDensityThresholdDep_of_le {t m : ℕ} (ht : 0 < t) (hm : 0 < m)
    (hmt : m ≤ 2 ^ 8 * t) : cutoff m < collatzDensityThresholdDep t := by
  have hB := heightExponent_lt_two_pow_sixteen_mul_seedBound_pow_three hm
  have hT := two_pow_sixtyFive_mul_seedBound_one_pow_lt
  have hU := seedBound_eq_mul m
  have hM1 : 1 ≤ seedBound 1 := one_le_seedBound one_pos
  have hUlt : seedBound m < 2 ^ seedBound m := Nat.lt_two_pow_self
  have hU1 : 1 ≤ seedBound m := one_le_seedBound hm
  rw [cutoff_def, collatzDensityThresholdDep]
  generalize 2 ^ 2 ^ 2 ^ 87640 = T at hT ⊢
  generalize heightExponent m = B at hB ⊢
  generalize seedBound m = U at hB hU hUlt hU1 ⊢
  generalize seedBound 1 = M at hT hU hM1
  have h1 : 32 * (2 ^ B * U + 1) < 2 ^ (6 + B + U) := by
    have hpos : 1 ≤ 2 ^ B * U := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [pow_add, pow_add]
    calc 32 * (2 ^ B * U + 1) ≤ 64 * (2 ^ B * U) := by omega
      _ < 64 * (2 ^ B * 2 ^ U) := by
        apply Nat.mul_lt_mul_of_pos_left _ (by norm_num)
        exact Nat.mul_lt_mul_of_pos_left hUlt (by positivity)
      _ = 2 ^ 6 * 2 ^ B * 2 ^ U := by ring
  have h2 : 6 + B + U < t ^ 3 * T := by
    have hU3 : U ≤ U ^ 3 := by
      calc U = U ^ 1 := (pow_one U).symm
        _ ≤ U ^ 3 := Nat.pow_le_pow_right hU1 (by norm_num)
    have hU31 : 1 ≤ U ^ 3 := Nat.one_le_pow _ _ hU1
    have hm3 : m ^ 3 ≤ 2 ^ 24 * t ^ 3 := by
      calc m ^ 3 ≤ (2 ^ 8 * t) ^ 3 := Nat.pow_le_pow_left hmt 3
        _ = 2 ^ 24 * t ^ 3 := by ring
    have ht3 : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ ht
    have hM3 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by norm_num)
    calc 6 + B + U < 2 ^ 17 * U ^ 3 := by omega
      _ = m ^ 3 * (2 ^ 17 * M ^ 3) := by rw [hU]; ring
      _ ≤ (2 ^ 24 * t ^ 3) * (2 ^ 17 * M ^ 3) := Nat.mul_le_mul_right _ hm3
      _ = t ^ 3 * (2 ^ 41 * M ^ 3) := by ring
      _ ≤ t ^ 3 * (2 ^ 65 * M ^ 4) := by
        apply Nat.mul_le_mul_left
        calc 2 ^ 41 * M ^ 3 ≤ 2 ^ 65 * M ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
          _ ≤ 2 ^ 65 * M ^ 4 := Nat.mul_le_mul_left _ hM3
      _ < t ^ 3 * T := Nat.mul_lt_mul_of_pos_left hT (by omega)
  exact h1.trans (Nat.pow_lt_pow_right (by norm_num) h2)

/-- For `t` prime to `3` there is an exponent `3 ≤ d ≤ 8` with `2^d t ≡ 4` or `7 (mod 9)`. -/
@[collatz_pos_dens "lem_two_pow_mod_nine"]
theorem exists_two_pow_mul_mod_nine {t : ℕ} (ht : ¬ 3 ∣ t) :
    ∃ d, 3 ≤ d ∧ d ≤ 8 ∧ ((2 ^ d * t) % 9 = 4 ∨ (2 ^ d * t) % 9 = 7) := by
  have h3 : t % 3 ≠ 0 := fun h => ht (Nat.dvd_of_mod_eq_zero h)
  have key : t % 9 = 1 ∨ t % 9 = 2 ∨ t % 9 = 4 ∨ t % 9 = 5 ∨ t % 9 = 7 ∨ t % 9 = 8 := by omega
  rcases key with h | h | h | h | h | h
  · exact ⟨4, by norm_num, by norm_num, by simp only [Nat.reducePow]; omega⟩
  · exact ⟨3, by norm_num, by norm_num, by simp only [Nat.reducePow]; omega⟩
  · exact ⟨6, by norm_num, by norm_num, by simp only [Nat.reducePow]; omega⟩
  · exact ⟨3, by norm_num, by norm_num, by simp only [Nat.reducePow]; omega⟩
  · exact ⟨4, by norm_num, by norm_num, by simp only [Nat.reducePow]; omega⟩
  · exact ⟨5, by norm_num, by norm_num, by simp only [Nat.reducePow]; omega⟩

/-- Changing the endpoint from `m` to `t`: if an orbit reaches `m` from `n` in `r` steps, with
`r` within `⌊a log (n / m)⌋₊`, and `a log (m / t) ≥ c`, then `r + c ≤ ⌊a log (n / t)⌋₊`. -/
@[collatz_pos_dens "lem_floor_log_shift"]
theorem add_le_floor_log_of_le_floor_log {a : ℝ} {n m t r c : ℕ} (hn : 0 < n) (hm : 0 < m)
    (ht : 0 < t) (hr : r ≤ ⌊a * Real.log ((n : ℝ) / m)⌋₊) (hnm : r = 0 → n = m)
    (hc : (c : ℝ) ≤ a * Real.log ((m : ℝ) / t)) :
    r + c ≤ ⌊a * Real.log ((n : ℝ) / t)⌋₊ := by
  have hsplit : Real.log ((n : ℝ) / t) = Real.log ((n : ℝ) / m) + Real.log ((m : ℝ) / t) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  apply Nat.le_floor
  push_cast
  by_cases hX : 0 ≤ a * Real.log ((n : ℝ) / m)
  · have h := (Nat.cast_le (α := ℝ).2 hr).trans (Nat.floor_le hX)
    rw [hsplit, mul_add]
    linarith
  · push Not at hX
    rw [Nat.floor_eq_zero.2 (by linarith)] at hr
    obtain rfl := hnm (by omega)
    rw [div_self (by positivity), Real.log_one, mul_zero] at hX
    exact absurd hX (lt_irrefl 0)

end CollatzPosDens

open CollatzPosDens

/-- **The joint density theorem for an endpoint prime to three.** For `t` not divisible by `3`
and every `N ≥ X(t)`, at least `c(t) · N` of the odd `n ∈ {0, …, N - 1}` reach `t` within
`⌊10.46 log (n / t)⌋₊` Collatz steps and reach the odd part of `t` within
`⌊3.4881 log (n / t)⌋₊` accelerated Collatz steps. -/
@[collatz_pos_dens "thm_endpoint_not_three_dvd"]
theorem positive_density_collatz_and_collatzAccel_reaches_of_not_three_dvd
    {t : ℕ} (ht : ¬3 ∣ t) {N : ℕ} (hN : collatzDensityThresholdDep t ≤ N) :
    collatzDensityDep t * N ≤
    #{n ∈ range N | Odd n ∧ ReachWithin collatz t n ⌊(10.46 : ℝ) * Real.log (n / t)⌋₊ ∧
      ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
        ⌊(3.4881 : ℝ) * Real.log (n / t)⌋₊} := by
  have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; exact ht (dvd_zero 3))
  obtain ⟨d, hd3, hd8, hd9⟩ := exists_two_pow_mul_mod_nine ht
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ d * t := ⟨_, rfl⟩
  rw [← hP] at hd9
  have hP8 : 8 * t ≤ P := by
    rw [hP]
    exact Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hd3)
  have hP256 : P ≤ 256 * t := by
    rw [hP]
    exact Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hd8)
  have hP2 : P % 2 = 0 := by
    rw [hP]
    exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) t)
  obtain ⟨m, hm⟩ : ∃ m, m = (P - 1) / 3 := ⟨_, rfl⟩
  have h3m : 3 * m + 1 = P := by omega
  have hm3 : ¬ 3 ∣ m := by omega
  have hmodd : Odd m := Nat.odd_iff.2 (by omega)
  have hm0 : 0 < m := by omega
  have hm256 : m ≤ 2 ^ 8 * t := by norm_num; omega
  have h4m : 2 ^ d * t ≤ 4 * m := by rw [← hP]; omega
  -- the logarithmic margin `log (m / t) ≥ (d - 2) log 2`
  have hL : (2 : ℝ) ^ d / 4 ≤ (m : ℝ) / t := by
    have h4m' : (2 : ℝ) ^ d * t ≤ 4 * m := by exact_mod_cast h4m
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hLm : ((d : ℝ) - 2) * Real.log 2 ≤ Real.log ((m : ℝ) / t) := by
    have := Real.log_le_log (by positivity) hL
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow, hlog4] at this
    linarith
  have hd3r : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  have hlog2 := Real.log_two_gt_d9
  have hprod : ((d : ℝ) - 2) * 0.6931471803 ≤ ((d : ℝ) - 2) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2.le (by linarith)
  -- the two orbit continuations from `m`
  have hcol : collatz^[1 + d] m = t := by
    rw [add_comm, Function.iterate_add_apply, Function.iterate_one, collatz_of_odd hmodd, h3m, hP,
      collatz_iterate_two_pow_mul]
  have hacc : collatzAccel m = t / 2 ^ padicValNat 2 t := by
    unfold collatzAccel
    rw [h3m, hP, padicValNat.mul (by positivity) ht0.ne', padicValNat.prime_pow, pow_add,
      Nat.mul_div_mul_left _ _ (by positivity)]
  have h1 : (10.46 : ℝ) = 1046 / 100 := by norm_num
  have h2 : (3.4881 : ℝ) = 34881 / 10000 := by norm_num
  rw [h1, h2]
  set c := #{n ∈ range N | Odd n ∧
      ReachWithin collatz t n ⌊(1046 / 100 : ℝ) * Real.log ((n : ℝ) / t)⌋₊ ∧
      ReachWithin collatzAccel (t / 2 ^ padicValNat 2 t) n
        ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / t)⌋₊} with hc
  have hcut : cutoff m ≤ N :=
    (cutoff_lt_collatzDensityThresholdDep_of_le ht0 hm0 hm256).le.trans hN
  have hM := densityConst_mul_le_ncard_reach hm0 hmodd hm3 (X := (N : ℝ)) (by exact_mod_cast hcut)
  have hle : {n : ℕ | 1 ≤ n ∧ (n : ℝ) < N ∧
        (Odd n ∧ ReachWithin collatz m n ⌊(523 / 50 : ℝ) * Real.log ((n : ℝ) / m)⌋₊ ∧
          ReachWithin collatzAccel m n
            ⌊(34881 / 10000 : ℝ) * Real.log ((n : ℝ) / m)⌋₊)}.ncard ≤ c := by
    rw [hc, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    rintro n ⟨hn1, hnN, hodd, ⟨r, hr, hrn⟩, ⟨r', hr', hrn'⟩⟩
    have h : (523 / 50 : ℝ) = 1046 / 100 := by norm_num
    rw [h] at hr
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨by exact_mod_cast hnN, hodd, ⟨r + (1 + d), ?_, ?_⟩, ⟨r' + 1, ?_, ?_⟩⟩
    · refine add_le_floor_log_of_le_floor_log (by omega) hm0 ht0 hr ?_ ?_
      · rintro rfl
        simpa using hrn
      · push_cast
        linarith
    · rw [show r + (1 + d) = (1 + d) + r by ring, Function.iterate_add_apply, hrn, hcol]
    · refine add_le_floor_log_of_le_floor_log (by omega) hm0 ht0 hr' ?_ ?_
      · rintro rfl
        simpa using hrn'
      · push_cast
        linarith
    · rw [show r' + 1 = 1 + r' by ring, Function.iterate_add_apply, hrn', Function.iterate_one,
        hacc]
  have hMc : densityConst m * N ≤ (c : ℝ) := hM.trans (by exact_mod_cast hle)
  have hcd : ((collatzDensityDep t : ℚ) : ℝ) ≤ densityConst m :=
    (collatzDensityDep_lt_densityConst_of_le ht0 hm0 hm256).le
  have hR : ((collatzDensityDep t : ℚ) : ℝ) * N ≤ (c : ℝ) :=
    (mul_le_mul_of_nonneg_right hcd (Nat.cast_nonneg N)).trans hMc
  exact_mod_cast hR
