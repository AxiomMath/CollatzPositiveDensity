/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import CollatzPosDens.Recipe.Tower
public import CollatzPosDens.Recipe.X0
public import CollatzPosDens.Recipe.CM
public import CollatzPosDens.Recipe.X0Tower
public import CollatzPosDens.Recipe.InvcTower
public import CollatzPosDens.Main.CountSuperset
public import CollatzPosDens.Main.MnInternal

/-!
# The explicit joint density theorem

For every natural number `N ≥ collatzDensityThreshold = tow_4(140214)`, at least
`collatzDensity · N` of the integers `n ∈ {0, …, N - 1}` reach `1` within `⌊10.46 log n⌋₊` Collatz
steps and have odd part reaching `1` within `⌊3.4881 log n⌋₊` accelerated Collatz steps, where
`collatzDensity = 1 / tow_3(140214)`.

The proof applies the joint count `densityConst · X ≤ #{…}` at `X = N`, valid since
`cutoff ≤ 1024 · cutoff < tow_4(140214) ≤ N`, enlarges the counted set, and replaces
`densityConst` by the smaller `collatzDensity`, using `1 / densityConst < tow_3(140214)`.

## Main results

* `positive_density_collatz_and_collatzAccel_reaches_one`: for `N ≥ collatzDensityThreshold`, at
  least `collatzDensity · N` of the `n < N` reach `1` within the stated Collatz and accelerated
  Collatz step bounds.

## Implementation notes

The inequality is stated in `ℚ`; it is proved in `ℝ` and transported back, since the inclusion
`ℚ → ℝ` preserves and reflects order. The towers `2 ^ 2 ^ 2 ^ 140214` and `2 ^ 2 ^ 2 ^ 2 ^ 140214`
are only ever rewritten symbolically, never evaluated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset CollatzPosDens

/-- The tower of four `2`'s over `x`, `2 ^ 2 ^ 2 ^ 2 ^ x`. -/
private def towerFourTwos (x : ℕ) : ℕ :=
  2 ^ 2 ^ 2 ^ 2 ^ x

private theorem towerFourTwos_eq_tower (x : ℕ) : towerFourTwos x = tower 4 x :=
  rfl

private theorem collatzDensityThreshold_eq_towerFourTwos :
    collatzDensityThreshold = towerFourTwos 140214 :=
  rfl

/-- `collatzDensityThreshold = tow_4(140214)`. -/
private theorem collatzDensityThreshold_eq_tower :
    collatzDensityThreshold = tower 4 140214 :=
  collatzDensityThreshold_eq_towerFourTwos.trans (towerFourTwos_eq_tower 140214)

private theorem tower_three_eq (x : ℕ) : tower 3 x = 2 ^ 2 ^ 2 ^ x :=
  rfl

/-- `collatzDensity = 1 / tow_3(140214)` in `ℝ`. -/
private theorem collatzDensity_cast_eq_tower :
    (collatzDensity : ℝ) = 1 / (tower 3 140214 : ℝ) := by
  rw [tower_three_eq]
  unfold collatzDensity
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_pow,
    Nat.cast_ofNat]

/-- **The explicit joint density theorem**. For every `N ≥ collatzDensityThreshold`, at least
`collatzDensity · N` of the `n ∈ {0, …, N - 1}` reach `1` within `⌊10.46 log n⌋₊` Collatz steps
and have odd part reaching `1` within `⌊3.4881 log n⌋₊` accelerated Collatz steps. -/
@[collatz_pos_dens "thm_main_joint"]
theorem positive_density_collatz_and_collatzAccel_reaches_one
    (N : ℕ) (hN : collatzDensityThreshold ≤ N) :
    collatzDensity * N ≤
    #{n ∈ range N | CollatzOneWithin n ⌊(10.46 : ℝ) * Real.log n⌋₊ ∧
      CollatzAccelOneWithin n ⌊(3.4881 : ℝ) * Real.log n⌋₊} := by
  have h1 : (10.46 : ℝ) = 1046 / 100 := by norm_num
  have h2 : (3.4881 : ℝ) = 34881 / 10000 := by norm_num
  rw [h1, h2]
  set c := #{n ∈ range N | CollatzOneWithin n ⌊(1046 / 100 : ℝ) * Real.log n⌋₊ ∧
      CollatzAccelOneWithin n ⌊(34881 / 10000 : ℝ) * Real.log n⌋₊} with hc
  have hcut : cutoff ≤ N := by
    have h := thousand_twenty_four_mul_cutoff_lt_tower
    rw [collatzDensityThreshold_eq_tower] at hN
    have : cutoff ≤ 1024 * cutoff := Nat.le_mul_of_pos_left _ (by norm_num)
    exact (this.trans h.le).trans hN
  have hM := densityConst_mul_le_ncard_reach (X := (N : ℝ)) (by exact_mod_cast hcut)
  have hsub := count_superset N
  have hle : {n : ℕ | 1 ≤ n ∧ (n : ℝ) < N ∧
        (CollatzOneWithin n ⌊(523 / 50 : ℝ) * Real.log n⌋₊ ∧
          CollatzAccelOneWithin n ⌊(34881 / 10000 : ℝ) * Real.log n⌋₊)}.ncard ≤ c := by
    rw [hc, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    intro n hn
    refine hsub ⟨hn.1, ?_, hn.2.2⟩
    exact_mod_cast hn.2.1
  have hMc : densityConst * N ≤ (c : ℝ) := hM.trans (by exact_mod_cast hle)
  have hcd : (collatzDensity : ℝ) ≤ densityConst := by
    have hinv := inv_densityConst_lt_tower
    have hpos := densityConst_pos
    rw [collatzDensity_cast_eq_tower]
    rw [one_div_lt hpos (by linarith [one_div_pos.2 hpos])] at hinv
    exact hinv.le
  have hR : (collatzDensity : ℝ) * N ≤ (c : ℝ) :=
    (mul_le_mul_of_nonneg_right hcd (Nat.cast_nonneg N)).trans hMc
  exact_mod_cast hR
