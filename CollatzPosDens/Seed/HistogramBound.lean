/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.Seed.Histogram
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Seed.S05HistFiberBound
public import CollatzPosDens.Seed.S05ValuationCount
public import CollatzPosDens.Seed.S05WidthSumBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Interval

/-!
# The histogram bound

Let `t` be an odd positive integer, `n ≥ generationThreshold` and `q ≤ 2 * scale n`. Then for
every `y : ResidueGroup q`, writing `K_j = cap j` and `𝗀 = growthRatio`,
$$3^q\,\mathrm{residueHistogram}(t, n, q, y) < \frac{97}{128}\cdot 37170\,\sqrt n\;
  \mathsf g^{n/2} \sum_{j<n}(K_j+3).$$

Write `B' = ∑_{j < n} scale j` and `W' = ∑_{j < n} wd (scale j)`. Every word `w_j` of a central
history has length within `wd (scale j)` of `scale j`, so the depth `historyDepth h` of a central
history is one of the `2 W' + 1` integers of `[B' - W', B' + W']`, and
`2 W' + 1 < 37170 √n 𝗀^{n/2}`. At each depth the valuation sums take at most `∑_{j<n} (K_j + 3)`
values. Grouping the histories by the pair of their depth and valuation sum, and bounding each
class by `97/128`, gives the claim.

## Main results

* `CollatzPosDens.three_pow_mul_residueHistogram_lt`: the histogram bound.
* `CollatzPosDens.historyDepth_mem_Icc_of_mem_centralHistories`: the depth of a central history
  lies in `[B' - W', B' + W']`.

## Implementation notes

The power `𝗀^{n/2}` is the real power `(growthRatio : ℝ) ^ ((n : ℝ) / 2)`. The sums over
`j < n` are written over the entries `k : Fin n` of a history.

## References

* [Mazur, *Collatz positive density*]
-/
@[expose] public section

namespace CollatzPosDens

/-- The depth of a central history `h = (w_0, …, w_{n-1})` lies within `∑_{j<n} wd (scale j)` of
`∑_{j<n} scale j`. -/
theorem historyDepth_mem_Icc_of_mem_centralHistories {t : ℚ} {n : ℕ}
    {h : Fin n → Word} (hh : h ∈ centralHistories t n) :
    (historyDepth h : ℤ) ∈ Finset.Icc
      ((∑ k : Fin n, scale k : ℕ) - (∑ k : Fin n, wd (scale k) : ℕ) : ℤ)
      ((∑ k : Fin n, scale k : ℕ) + (∑ k : Fin n, wd (scale k) : ℕ)) := by
  have hmem := fun k : Fin n => selectedTuples_mem_centralFamily hh.1 k
  have hlo := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
    sub_wd_le_length_of_mem_centralFamily (hmem k)
  have hhi := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
    length_le_add_wd_of_mem_centralFamily (hmem k)
  rw [Finset.sum_sub_distrib] at hlo
  rw [Finset.sum_add_distrib] at hhi
  rw [historyDepth_eq_sum, Finset.mem_Icc]
  push_cast
  exact ⟨hlo, by exact_mod_cast hhi⟩

/-- For an odd positive integer `t`, `n ≥ generationThreshold`, `q ≤ 2 * scale n` and
`y : ResidueGroup q`, `3^q · residueHistogram t n q y` is less than
`(97/128) · 37170 √n growthRatio^{n/2} ∑_{j<n} (cap j + 3)`. -/
@[collatz_pos_dens "lem_histogram_bound"]
theorem three_pow_mul_residueHistogram_lt {t : ℤ} (hodd : Odd t) (ht : 0 < t) {n q : ℕ}
    (hn : generationThreshold ≤ n) (hq : q ≤ 2 * scale n) (y : ResidueGroup q) :
    (3 : ℝ) ^ q * residueHistogram t n q y <
      97 / 128 * 37170 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) *
        ∑ j ∈ Finset.range n, ((cap j : ℝ) + 3) := by
  classical
  set P : (Fin n → Word) → Prop := fun h =>
    ∃ r : ℤ, (r : ℚ) = historyEndpoint t h ∧ (r : ResidueGroup q) = y
  set s := (centralHistories_finite (t : ℚ) n).toFinset.filter P
  have hHg : residueHistogram t n q y = ∑ h ∈ s, ((concatWord h).weight : ℝ) :=
    residueHistogram_eq_sum _ _ _ _
  have hs : ∀ h ∈ s, h ∈ centralHistories t n ∧ P h := fun h hh => by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hh
    exact hh
  set g : (Fin n → Word) → ℤ × ℤ := fun h =>
    ((historyDepth h : ℤ), ((concatWord h).valSum : ℤ))
  set T := s.image g
  have hclass : ∀ p ∈ T, (3 : ℝ) ^ q * ∑ h ∈ s with g h = p, ((concatWord h).weight : ℝ) <
      97 / 128 := by
    rintro ⟨D, A⟩ -
    have hset : ((s.filter fun h => g h = (D, A) : Finset _) :
        Set (Fin n → Word)) =
        {h | h ∈ centralHistories t n ∧ (historyDepth h : ℤ) = D ∧
          ((concatWord h).valSum : ℤ) = A ∧
          ∃ r : ℤ, (r : ℚ) = historyEndpoint t h ∧ (r : ResidueGroup q) = y} := by
      ext h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, s, Finset.mem_filter,
        Set.Finite.mem_toFinset, g, Prod.mk.injEq, P]
      exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, c, d, b⟩, fun ⟨a, c, d, b⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    rw [← finsum_mem_coe_finset, hset]
    exact three_pow_mul_finsum_weight_histFiber_le hodd ht hn hq y D A
  have hHgT : (3 : ℝ) ^ q * residueHistogram t n q y ≤ T.card * (97 / 128) := by
    rw [hHg, ← Finset.sum_fiberwise_of_maps_to (fun h hh => Finset.mem_image_of_mem g hh),
      Finset.mul_sum, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun p hp => (hclass p hp).le
  have hn1 : 1 ≤ n := le_trans (by rw [generationThreshold_def]; norm_num) hn
  set Bn : ℕ := ∑ k : Fin n, scale k
  set Wn : ℕ := ∑ k : Fin n, wd (scale k)
  set Sn : ℕ := ∑ j ∈ Finset.range n, (cap j + 3)
  set I : Finset ℤ := Finset.Icc ((Bn : ℤ) - Wn) ((Bn : ℤ) + Wn)
  set V : ℤ → Set ℕ := fun D => {a : ℕ | ∃ h ∈ centralHistories t n,
    (historyDepth h : ℤ) = D ∧ (concatWord h).valSum = a}
  have hTI : ∀ p ∈ T, p.1 ∈ I := by
    intro p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
    exact historyDepth_mem_Icc_of_mem_centralHistories (hs h hh).1
  have hfib : ∀ D ∈ I, (T.filter fun p => p.1 = D).card ≤ Sn := by
    intro D _
    obtain ⟨hfin, hle⟩ := centralHistories_valSum_atDepth_ncard_le (t : ℚ) hn1 D
    refine le_trans ?_ hle
    rw [Set.ncard_eq_toFinset_card _ hfin]
    refine Finset.card_le_card_of_injOn (fun p => p.2.toNat) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨⟨h, hh, rfl⟩, hD⟩ := hp.imp_left Finset.mem_image.1
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact ⟨h, (hs h hh).1, hD, Int.toNat_natCast _⟩
    · intro p hp p' hp' he
      rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
      obtain ⟨⟨h, -, rfl⟩, hD⟩ := hp.imp_left Finset.mem_image.1
      obtain ⟨⟨h', -, rfl⟩, hD'⟩ := hp'.imp_left Finset.mem_image.1
      simp only [g, Int.toNat_natCast] at he hD hD'
      simp only [g, Prod.mk.injEq]
      exact ⟨hD.trans hD'.symm, by exact_mod_cast he⟩
  have hIcard : I.card = 2 * Wn + 1 := by
    simp only [I, Int.card_Icc]
    omega
  have hTcard : T.card ≤ (2 * Wn + 1) * Sn := by
    rw [Finset.card_eq_sum_card_fiberwise hTI, ← hIcard, ← smul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ hfib
  have hWeq : (Wn : ℝ) = ∑ j ∈ Finset.range n, (wd (scale j) : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (wd (scale j) : ℝ))]
    push_cast [Wn]
    rfl
  have hW : 2 * (Wn : ℝ) + 1 < 37170 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) := by
    rw [hWeq]; exact two_mul_sum_wd_scale_add_one_lt hn
  have hS : (0 : ℝ) < Sn := by
    have : cap 0 + 3 ≤ Sn :=
      Finset.single_le_sum (f := fun j => cap j + 3) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 hn1)
    exact_mod_cast (by omega : 0 < Sn)
  have hSeq : (Sn : ℝ) = ∑ j ∈ Finset.range n, ((cap j : ℝ) + 3) := by
    simp only [Sn, Nat.cast_sum, Nat.cast_add, Nat.cast_ofNat]
  calc (3 : ℝ) ^ q * residueHistogram t n q y ≤ T.card * (97 / 128) := hHgT
    _ ≤ ((2 * Wn + 1) * Sn : ℕ) * (97 / 128) := by gcongr
    _ = 97 / 128 * (2 * (Wn : ℝ) + 1) * Sn := by push_cast; ring
    _ < 97 / 128 * (37170 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2)) * Sn :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hW (by norm_num)) hS
    _ = 97 / 128 * 37170 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) *
          ∑ j ∈ Finset.range n, ((cap j : ℝ) + 3) := by
        rw [hSeq]
        ring

end CollatzPosDens
