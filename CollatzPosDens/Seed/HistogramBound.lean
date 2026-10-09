/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.Histogram
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.CentralDepth
public import CollatzPosDens.Seed.HistFiberBound
public import CollatzPosDens.Seed.ValuationCount
public import CollatzPosDens.Seed.WidthSumBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Interval

/-!
# The histogram bound

Let `M` be an odd positive integer, `n ≥ 10000` and `q ≤ 2 * scale n`. Then for every
`y : ResidueGroup q`,
`3 ^ q * residueHistogram M n q y < 4075 / 56 * (277 / 128) * n ^ (5 / 2) * histogramGrowth ^ n`.

Write `B = ∑ j ∈ range n, scale j` and `W = ∑ j ∈ range n, dw (scale j)`. Every word of a
central history has length within `dw (scale j)` of `scale j`, so the `historyDepth` of a central
history is one of the `2 * W + 1` integers of `[B - W, B + W]`, and
`2 * W + 1 < 4075 * √n * histogramGrowth ^ n`. At each depth the valuation sums take fewer than
`n ^ 2 / 56` values. Grouping the histories by their depth and valuation sum and bounding each
class by `277 / 128` gives the claim.

## Main results

* `CollatzPosDens.three_pow_mul_residueHistogram_lt`: the histogram bound.
* `CollatzPosDens.three_pow_mul_residueHistogram_lt_historyDepth_mem_Icc`: the depth of a
  central history lies in `[B - W, B + W]`.

## Implementation notes

The power `n ^ (5 / 2)` is the real power `(n : ℝ) ^ (5 / 2 : ℝ)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The depth of a central history lies within `∑ j ∈ range n, dw (scale j)` of
`∑ j ∈ range n, scale j`. -/
theorem three_pow_mul_residueHistogram_lt_historyDepth_mem_Icc {M : ℚ} {n : ℕ}
    {h : Fin n → Word} (hh : h ∈ centralHistories M n) :
    (historyDepth h : ℤ) ∈ Finset.Icc
      ((∑ j ∈ Finset.range n, scale j : ℕ) - (∑ j ∈ Finset.range n, dw (scale j) : ℕ) : ℤ)
      ((∑ j ∈ Finset.range n, scale j : ℕ) + (∑ j ∈ Finset.range n, dw (scale j) : ℕ)) := by
  have hmem := fun j : Fin n => centralDepth_length_mem (selectedTuples_mem_centralFamily hh.1 j)
  have hlo := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (hmem j).1
  have hhi := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (hmem j).2
  rw [Finset.sum_sub_distrib] at hlo
  rw [Finset.sum_add_distrib] at hhi
  rw [historyDepth_eq_sum, Finset.mem_Icc, Finset.sum_range, Finset.sum_range]
  push_cast
  exact ⟨hlo, by exact_mod_cast hhi⟩

/-- **Histogram bound**. For an odd positive integer `M`, `n ≥ 10000`, `q ≤ 2 * scale n` and
`y : ResidueGroup q`, the histogram satisfies
`3 ^ q * residueHistogram M n q y < 4075 / 56 * (277 / 128) * n ^ (5 / 2) * histogramGrowth ^ n`.
-/
@[collatz_pos_dens "lem_histogram_bound"]
theorem three_pow_mul_residueHistogram_lt {M : ℤ} (hodd : Odd M) (hM : 0 < M) {n q : ℕ}
    (hn : 10000 ≤ n) (hq : q ≤ 2 * scale n) (y : ResidueGroup q) :
    (3 : ℝ) ^ q * residueHistogram M n q y <
      4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n := by
  classical
  set P : (Fin n → Word) → Prop := fun h =>
    ∃ r : ℤ, (r : ℚ) = historyEndpoint M h ∧ (r : ResidueGroup q) = y
  set s := (centralHistories_finite (M : ℚ) n).toFinset.filter P
  have hHg : residueHistogram M n q y = ∑ h ∈ s, ((concatWord h).weight : ℝ) :=
    residueHistogram_eq_sum _ _ _ _
  have hs : ∀ h ∈ s, h ∈ centralHistories M n ∧ P h := fun h hh =>
    (Finset.mem_filter.1 hh).imp_left (Set.Finite.mem_toFinset _).1
  set g : (Fin n → Word) → ℤ × ℤ := fun h =>
    ((historyDepth h : ℤ), ((concatWord h).valSum : ℤ))
  set T := s.image g
  have hclass : ∀ p ∈ T, (3 : ℝ) ^ q * ∑ h ∈ s with g h = p, ((concatWord h).weight : ℝ) ≤
      277 / 128 := by
    rintro ⟨D, A⟩ -
    have hset : ((s.filter fun h => g h = (D, A) : Finset _) : Set (Fin n → Word)) =
        {h | h ∈ centralHistories M n ∧ (historyDepth h : ℤ) = D ∧
          ((concatWord h).valSum : ℤ) = A ∧
          ∃ r : ℤ, (r : ℚ) = historyEndpoint M h ∧ (r : ResidueGroup q) = y} := by
      ext h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, s, Finset.mem_filter,
        Set.Finite.mem_toFinset, g, Prod.mk.injEq, P]
      tauto
    rw [← finsum_mem_coe_finset, hset]
    exact three_pow_mul_finsum_weight_histFiber_le hodd hM (by omega) hq y D A
  have hHgT : (3 : ℝ) ^ q * residueHistogram M n q y ≤ T.card * (277 / 128) := by
    rw [hHg, ← Finset.sum_fiberwise_of_maps_to (fun h hh => Finset.mem_image_of_mem g hh),
      Finset.mul_sum, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ hclass
  set Bn : ℕ := ∑ j ∈ Finset.range n, scale j
  set Wn : ℕ := ∑ j ∈ Finset.range n, dw (scale j)
  set I : Finset ℤ := Finset.Icc ((Bn : ℤ) - Wn) ((Bn : ℤ) + Wn)
  set V : ℤ → Set ℕ := fun D => {a : ℕ | ∃ h ∈ centralHistories M n,
    (historyDepth h : ℤ) = D ∧ (concatWord h).valSum = a}
  have hTI : ∀ p ∈ T, p.1 ∈ I := by
    intro p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
    exact three_pow_mul_residueHistogram_lt_historyDepth_mem_Icc (hs h hh).1
  have hfib : ∀ D ∈ I, ((T.filter fun p => p.1 = D).card : ℝ) ≤ (V D).ncard := by
    intro D _
    obtain ⟨hfin, -⟩ := centralHistories_valSum_atDepth_ncard_lt (M : ℚ) (by omega : 8058 ≤ n) D
    rw [Set.ncard_eq_toFinset_card _ hfin]
    norm_cast
    refine Finset.card_le_card_of_injOn (fun p => p.2.toNat) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨⟨h, hh, rfl⟩, hD⟩ := hp.imp_left Finset.mem_image.1
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact ⟨h, (hs h hh).1, hD, by simp [g]⟩
    · intro p hp p' hp' he
      rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
      obtain ⟨⟨h, -, rfl⟩, hD⟩ := hp.imp_left Finset.mem_image.1
      obtain ⟨⟨h', -, rfl⟩, hD'⟩ := hp'.imp_left Finset.mem_image.1
      simp only [g, Int.toNat_natCast] at he hD hD'
      simp only [g, Prod.mk.injEq]
      exact ⟨hD.trans hD'.symm, by exact_mod_cast he⟩
  have hIcard : (I.card : ℝ) = 2 * Wn + 1 := by
    simp only [I, Int.card_Icc]
    rw [show ((Bn : ℤ) + Wn + 1 - (Bn - Wn)).toNat = 2 * Wn + 1 by omega]
    push_cast
    ring
  have hTcard : (T.card : ℝ) < (2 * Wn + 1) * ((n : ℝ) ^ 2 / 56) := by
    rw [Finset.card_eq_sum_card_fiberwise hTI]
    push_cast
    calc ∑ D ∈ I, ((T.filter fun p => p.1 = D).card : ℝ) ≤ ∑ D ∈ I, ((V D).ncard : ℝ) :=
          Finset.sum_le_sum hfib
      _ < ∑ _D ∈ I, (n : ℝ) ^ 2 / 56 :=
          Finset.sum_lt_sum_of_nonempty ⟨Bn, by simp [I]⟩ fun D _ =>
            (centralHistories_valSum_atDepth_ncard_lt (M : ℚ) (by omega : 8058 ≤ n) D).2
      _ = (2 * Wn + 1) * ((n : ℝ) ^ 2 / 56) := by
          rw [Finset.sum_const, nsmul_eq_mul, hIcard]
  have hW : 2 * (Wn : ℝ) + 1 < 4075 * √(n : ℝ) * histogramGrowth ^ n := by
    simpa [Wn] using two_mul_sum_dw_scale_add_one_lt hn
  have hpow : (n : ℝ) ^ (5 / 2 : ℝ) = √(n : ℝ) * (n : ℝ) ^ 2 := by
    rw [show (5 / 2 : ℝ) = 1 / 2 + 2 by norm_num,
      Real.rpow_add' (Nat.cast_nonneg n) (by norm_num), Real.sqrt_eq_rpow]
    norm_cast
  calc (3 : ℝ) ^ q * residueHistogram M n q y ≤ T.card * (277 / 128) := hHgT
    _ < (2 * Wn + 1) * ((n : ℝ) ^ 2 / 56) * (277 / 128) := by gcongr
    _ ≤ 4075 * √(n : ℝ) * histogramGrowth ^ n * ((n : ℝ) ^ 2 / 56) * (277 / 128) := by
        gcongr
    _ = 4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n := by
        rw [hpow]
        ring

end CollatzPosDens
