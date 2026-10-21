/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrPassageBound
public import CollatzPosDens.StoppingTrace.TrGapThreePassage
public import CollatzPosDens.StoppingTrace.TrDSmall
public import CollatzPosDens.StoppingTrace.TrDTail

/-!
# One passage at every gap

Fix a level `n` and a unit `ξ ∈ G_n`, and let "black" refer to the colour scale `ε_*`. For every
black `v ∈ 𝒫`, with `s = gap(v)`,
```
∑_{π ∈ Π_s} bw^⊗(π) exp(-γ_* N^*(v, π; |π|)) ≤ 96338641 / 10^8.
```

Put `d₀ = 3661359 / 10^8`, so that `1 - d₀ = 96338641 / 10^8`. At the gap `s = 3`,
`tsum_trPassage_three_mul_exp_neg_trCount_le` gives the deficit `37/160 ≥ d₀`. At every other gap,
`tsum_trPassage_mul_exp_neg_trCount_le` gives the deficit `D_cr(s)`, and `D_cr(s) ≥ d₀`:

* for `s ≥ 512`, `D_cr(s) ≥ 3927606451461 / 16777216000000`;
* for `2 ≤ s ≤ 511`, `s ∉ {3, 6, 9, 13, 16}`, `D_cr(s) ≥ 61817834604121 / 268435456000000`;
* for `s ∈ {0, 1, 6, 9, 13, 16}`, `D_cr(s)` is an explicit rational, a sum of nonnegative terms
  `W_j G(f_s, s - j)` and two nonnegative corrections, where `W_j` collects the packet deficits
  `ϖ(c) δ^{pk}_{c,o}` with `c - o = j` and `G(f, t) = ∑_{r=1}^{f} 𝖱(r - 1, t)`. A single term
  already exceeds `d₀`: `W_0 G(1, 0) = W_0 = 59987721 / 1638400000` at `s = 0` (this is all of
  `D_cr(0)`), `W_1 G(1, 0) = W_1` at `s = 1`, and `W_2 G(f_s, s - 2)` at `s ∈ {6, 9, 13, 16}`.

## Main results

* `CollatzPosDens.le_trDirectCrossing_of_ne_three`: `D_cr(s) ≥ 3661359 / 10^8` for `s ≠ 3`.
* `CollatzPosDens.tsum_trPassage_mul_exp_neg_trCount_le_of_bkBlack`: the passage bound at every
  gap.

## Implementation notes

At the six exceptional gaps the exact values of `D_cr(s)` are not needed: the decrement is bounded
below by one term of its expansion over the differences `j = c - o`, and that term is a product of
an entry of the table of the weights `W_j` and a ratio of a binomial prefix sum, computed in
natural numbers, to a power of two.

## References

* [Mazur, *Collatz positive density*], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The partial raw-prefix mass `G(f, t)` is nonnegative. -/
theorem exitSumQ_nonneg (f : ℕ) (t : ℤ) : 0 ≤ exitSumQ f t := by
  unfold exitSumQ
  split_ifs <;> positivity

/-- The correction `δ^{rep}_{s,3,1} - δ^{pk}_{3,1}` is nonnegative. -/
theorem repCorrThree_nonneg (s : ℕ) : 0 ≤ repCorrThree s := by
  unfold repCorrThree
  linarith [le_max_left (1 / 2 : ℚ) (1 - raw3CapQ s)]

/-- The weights `W_j` are nonnegative. -/
theorem weightTable_getD_nonneg (j : ℕ) : 0 ≤ weightTable.getD j 0 := by
  by_cases hj : j ∈ range 16
  · rw [weightTable_eq j hj]
    positivity
  · rw [List.getD_eq_default _ _ (by simp only [mem_range] at hj; simp [weightTable]; omega)]

/-- Each term `W_j G(f_s, s - j)`, `j < 16`, of the expansion of `D_cr(s)` is at most `D_cr(s)`. -/
theorem weightTable_mul_exitSumQ_le_crossingQ (s : ℕ) {j : ℕ} (hj : j < 16) :
    weightTable.getD j 0 * exitSumQ (bkExitWidth s) ((s : ℤ) - j) ≤ crossingQ s := by
  have h₁ : weightTable.getD j 0 * exitSumQ (bkExitWidth s) ((s : ℤ) - j) ≤
      ∑ i ∈ range 16, weightTable.getD i 0 * exitSumQ (bkExitWidth s) ((s : ℤ) - i) :=
    single_le_sum (f := fun i ↦ weightTable.getD i 0 * exitSumQ (bkExitWidth s) ((s : ℤ) - i))
      (fun i _ ↦ mul_nonneg (weightTable_getD_nonneg i) (exitSumQ_nonneg _ _)) (mem_range.2 hj)
  have h₃ : 0 ≤ 1 / 4 * repCorrThree s * exitSumQ (bkExitWidth s) ((s : ℤ) - 2) := by
    have := repCorrThree_nonneg s
    have := exitSumQ_nonneg (bkExitWidth s) ((s : ℤ) - 2)
    positivity
  have h₄ : 0 ≤ 3 / 16 * repCorrFour s * exitSumQ (bkExitWidth s) ((s : ℤ) - 3) := by
    have := repCorrFour_nonneg s
    have := exitSumQ_nonneg (bkExitWidth s) ((s : ℤ) - 3)
    positivity
  rw [crossingQ]
  linarith

/-- A term `W_j G(f, t)` of the expansion of `D_cr(t + j)` with `t ≥ 1`, its binomial prefix sum
`N = ∑_{k < f - 1} binom(t - 1, 2k + 1)` given in natural numbers, bounds `D_cr(t + j)`. -/
private theorem weightTable_mul_div_le_crossingQ {s j f t N : ℕ} (hj : j < 16) (hs : s = t + j)
    (hf : bkExitWidth s = f) (ht : 0 < t) (hN : (oddChooseAcc (t - 1) (f - 1)).2 = N) :
    weightTable.getD j 0 * ((N : ℚ) / 2 ^ t) ≤ crossingQ s := by
  have h := weightTable_mul_exitSumQ_le_crossingQ s hj
  have he : exitSumQ (bkExitWidth s) ((s : ℤ) - j) = (N : ℚ) / 2 ^ t := by
    rw [exitSumQ, hf, show (s : ℤ) - j = t by omega]
    simp only [show ¬((t : ℤ) ≤ 0) by omega, ↓reduceIte]
    rw [Int.toNat_natCast, hN]
    push_cast
    rfl
  rwa [he] at h

/-- `D_cr(s) ≥ 3661359 / 10^8` at the six gaps `s ∈ {0, 1, 6, 9, 13, 16}`. -/
private theorem le_crossingQ_of_mem_exceptional {s : ℕ}
    (hs : s ∈ ({0, 1, 6, 9, 13, 16} : Finset ℕ)) : (3661359 / 10 ^ 8 : ℚ) ≤ crossingQ s := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · -- `s = 0`: the term `W_0 G(1, 0) = W_0`.
    refine le_trans ?_ (weightTable_mul_exitSumQ_le_crossingQ 0 (j := 0) (by norm_num))
    norm_num [weightTable, exitSumQ, bkExitWidth_def]
  · -- `s = 1`: the term `W_1 G(1, 0) = W_1`.
    refine le_trans ?_ (weightTable_mul_exitSumQ_le_crossingQ 1 (j := 1) (by norm_num))
    norm_num [weightTable, exitSumQ, bkExitWidth_def]
  · -- `s = 6`: the term `W_2 G(2, 4) = W_2 · 3 / 2^4`.
    refine le_trans ?_ (weightTable_mul_div_le_crossingQ (j := 2) (f := 2) (t := 4) (N := 3)
      (by norm_num) rfl rfl (by norm_num) (by decide))
    norm_num [weightTable]
  · -- `s = 9`: the term `W_2 G(3, 7) = W_2 · 26 / 2^7`.
    refine le_trans ?_ (weightTable_mul_div_le_crossingQ (j := 2) (f := 3) (t := 7) (N := 26)
      (by norm_num) rfl rfl (by norm_num) (by decide))
    norm_num [weightTable]
  · -- `s = 13`: the term `W_2 G(5, 11) = W_2 · 502 / 2^11`.
    refine le_trans ?_ (weightTable_mul_div_le_crossingQ (j := 2) (f := 5) (t := 11) (N := 502)
      (by norm_num) rfl rfl (by norm_num) (by decide))
    norm_num [weightTable]
  · -- `s = 16`: the term `W_2 G(6, 14) = W_2 · 4017 / 2^14`.
    refine le_trans ?_ (weightTable_mul_div_le_crossingQ (j := 2) (f := 6) (t := 14) (N := 4017)
      (by norm_num) rfl rfl (by norm_num) (by decide))
    norm_num [weightTable]

/-- **The first-crossing decrement off the gap three.** For every gap `s ≠ 3`,
`D_cr(s) ≥ 3661359 / 10^8`. -/
theorem le_trDirectCrossing_of_ne_three {s : ℕ} (hs : s ≠ 3) :
    (3661359 / 10 ^ 8 : ℝ) ≤ trDirectCrossing s := by
  by_cases h₅₁₂ : 512 ≤ s
  · exact le_trans (by norm_num) (trDirectCrossing_ge h₅₁₂)
  by_cases hex : s ∈ ({0, 1, 6, 9, 13, 16} : Finset ℕ)
  · rw [trDirectCrossing_eq_crossingQ,
      show (3661359 / 10 ^ 8 : ℝ) = ((3661359 / 10 ^ 8 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_le.2 (le_crossingQ_of_mem_exceptional hex)
  · have hne : s ∉ ({3, 6, 9, 13, 16} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hex ⊢
      omega
    have h₂ : 2 ≤ s := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hex
      omega
    exact le_trans (by norm_num) (le_trDirectCrossing_of_le_511 h₂ (by omega) hne)

/-- **One passage at every gap.** Let `ξ ∈ G_n` be a unit, `v ∈ 𝒫` black (at the colour scale
`ε_*`) and `s = gap(v)`. Then
`∑_{π ∈ Π_s} bw^⊗(π) exp(-γ_* N^*(v, π; |π|)) ≤ 96338641 / 10^8`. -/
@[collatz_pos_dens "lem_tr_passage_all"]
theorem tsum_trPassage_mul_exp_neg_trCount_le_of_bkBlack {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v) :
    ∑' π : trPassage (trGap n ξ (epsStar : ℝ) v).toNat,
        trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) ≤
      96338641 / 10 ^ 8 := by
  by_cases h₃ : trGap n ξ (epsStar : ℝ) v = 3
  · have h := tsum_trPassage_three_mul_exp_neg_trCount_le hξ hv hb h₃
    rw [h₃, show (3 : ℤ).toNat = 3 from rfl]
    linarith
  · have hs : (trGap n ξ (epsStar : ℝ) v).toNat ≠ 3 := by
      have := trGap_nonneg n ξ (epsStar : ℝ) v
      omega
    have h := tsum_trPassage_mul_exp_neg_trCount_le hξ hv hb
    have hD := le_trDirectCrossing_of_ne_three hs
    linarith

end CollatzPosDens
