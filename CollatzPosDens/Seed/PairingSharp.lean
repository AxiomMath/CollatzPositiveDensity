/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FcCapSumProp
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhHhist
public import CollatzPosDens.Seed.Histogram
public import CollatzPosDens.Seed.HistogramBound
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# The sharp pairing estimate

Let `t` be an odd positive integer, `n ≥ N_*`, `0 ≤ q ≤ 2 b_n`, let `𝓗' ⊆ 𝓗_n(t)` and
`f : G_q → ℝ`. Then
$$\sum_{h ∈ 𝓗'} ω(h)\,|f(R_h \bmod 3^q)| \le
  \mathcal H_{\mathrm{hist}}\, n^{5/2}\, \mathsf g^{n/2}\, ⟨|f|⟩_q.$$
Grouping the histories by the residue `y = R_h mod 3^q` bounds the left side by
`∑_y Hg_{n,q}(y) |f(y)| ≤ max_y (3^q Hg_{n,q}(y)) ⟨|f|⟩_q`. The histogram bound gives
`3^q Hg_{n,q}(y) < (97/128) · 37170 √n 𝗀^{n/2} ∑_{j<n} (K_j + 3)`, and the sum of the shifted
caps `∑_{j<n} (K_j + 3) < 1 + ∑_{j<n} (K_j + 3) < n^2/82` (valid for `n ≥ N_* = 9853`) turns
this into `𝓗_hist n^{5/2} 𝗀^{n/2}`, by the exact comparison
`97 · 37170 / (128 · 82) = 1802745/5248 ≤ 1805312/5248 = 344 = 𝓗_hist`.

## Main results

* `CollatzPosDens.exists_historyEndpoint_eq_intCast`: the endpoint of a central history from a
  positive odd integer is an integer.
* `CollatzPosDens.finsum_weight_mul_abs_le_of_three_pow_mul_residueHistogram_le`: the pairing
  estimate with any uniform bound `C` on `3^q Hg_{n,q}(y)` in place of `𝓗_hist n^{5/2} 𝗀^{n/2}`.
* `CollatzPosDens.three_pow_mul_residueHistogram_lt_Hhist`: `3^q Hg_{n,q}(y) < 𝓗_hist n^{5/2}
  𝗀^{n/2}` for `n ≥ N_*`.
* `CollatzPosDens.finsum_weight_mul_abs_le_Hhist`: the sharp pairing estimate.

## Implementation notes

The endpoint `R_h` is a rational number, an integer for `h ∈ 𝓗_n(t)` since the concatenated
word is admissible from `t`; its residue modulo `3^q` is taken to be that of its numerator. The
sum over `𝓗'` is a `finsum` over a set, finite since `𝓗' ⊆ 𝓗_n(t)`. The power `n^{5/2}` is the
real power `(n : ℝ) ^ (5 / 2 : ℝ)`, and `𝗀^{n/2}` is the real power
`(growthRatio : ℝ) ^ ((n : ℝ) / 2)`.

## References

* [Mazur, *Collatz positive density*], §16.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The endpoint of a central history from a positive odd integer `t` is an integer. -/
theorem exists_historyEndpoint_eq_intCast {t : ℤ} (hodd : Odd t) (ht : 0 < t) {n : ℕ}
    {h : Fin n → Word} (hh : h ∈ centralHistories t n) :
    ∃ m : ℤ, historyEndpoint t h = m := by
  obtain ⟨m, hm, -⟩ := hh.2.exists_src_eq_pos_odd ht hodd
  exact ⟨m, (historyEndpoint_eq_src _ h).trans hm⟩

/-- The pairing estimate with an arbitrary uniform bound: if `3^q Hg_{n,q}(y) ≤ C` for every
`y ∈ G_q`, then for every set `𝓗' ⊆ 𝓗_n(t)` and `f : G_q → ℝ`,
`∑_{h ∈ 𝓗'} ω(h) |f(R_h mod 3^q)| ≤ C ⟨|f|⟩_q`. -/
theorem finsum_weight_mul_abs_le_of_three_pow_mul_residueHistogram_le {t : ℤ} (hodd : Odd t)
    (ht : 0 < t) {n q : ℕ} {C : ℝ}
    (hC : ∀ y : ResidueGroup q, (3 : ℝ) ^ q * residueHistogram t n q y ≤ C)
    {H' : Set (Fin n → Word)} (hH' : H' ⊆ centralHistories t n)
    (f : ResidueGroup q → ℝ) :
    ∑ᶠ h ∈ H', ((concatWord h).weight : ℝ) *
        |f ((historyEndpoint t h).num : ResidueGroup q)| ≤
      C * residueAvg q (fun y => |f y|) := by
  classical
  have hfin : H'.Finite := (centralHistories_finite t n).subset hH'
  set s := hfin.toFinset
  set r : (Fin n → Word) → ResidueGroup q :=
    fun h => ((historyEndpoint t h).num : ResidueGroup q)
  have h3 : (0 : ℝ) < 3 ^ q := by positivity
  -- each residue class of `𝓗'` weighs at most `Hg_{n,q}(y) ≤ C / 3^q`
  have hclass : ∀ y, ∑ h ∈ s with r h = y, ((concatWord h).weight : ℝ) ≤ C / 3 ^ q := by
    intro y
    set S : Set (Fin n → Word) := {h | h ∈ centralHistories t n ∧
        ∃ m : ℤ, (m : ℚ) = historyEndpoint t h ∧ (m : ResidueGroup q) = y}
    have hSfin : S.Finite :=
      (centralHistories_finite t n).subset fun h hh => hh.1
    have hHg : residueHistogram t n q y =
        ∑ h ∈ hSfin.toFinset, ((concatWord h).weight : ℝ) :=
      finsum_mem_eq_finite_toFinset_sum _ hSfin
    have hsub : s.filter (fun h => r h = y) ⊆ hSfin.toFinset := by
      intro h hh
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hh
      obtain ⟨hh, hry⟩ := hh
      have hc := hH' hh
      obtain ⟨m, hm⟩ := exists_historyEndpoint_eq_intCast hodd ht hc
      rw [Set.Finite.mem_toFinset]
      refine ⟨hc, m, hm.symm, ?_⟩
      have : (historyEndpoint t h).num = m := by
        rw [hm, Rat.num_intCast]
      simpa [r, this] using hry
    calc ∑ h ∈ s with r h = y, ((concatWord h).weight : ℝ)
        ≤ ∑ h ∈ hSfin.toFinset, ((concatWord h).weight : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by
            exact_mod_cast (Word.weight_pos _).le
      _ = residueHistogram t n q y := hHg.symm
      _ ≤ C / 3 ^ q := by
          rw [le_div_iff₀ h3, mul_comm]
          exact hC y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    ← Finset.sum_fiberwise_of_maps_to (g := r) (t := Finset.univ) fun _ _ => Finset.mem_univ _]
  calc ∑ y, ∑ h ∈ s with r h = y, ((concatWord h).weight : ℝ) * |f (r h)|
      = ∑ y, |f y| * ∑ h ∈ s with r h = y, ((concatWord h).weight : ℝ) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [(Finset.mem_filter.mp hh).2, mul_comm]
    _ ≤ ∑ y, |f y| * (C / 3 ^ q) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hclass y) (abs_nonneg _)
    _ = C * residueAvg q (fun y => |f y|) := by
        rw [residueAvg_def, ← Finset.sum_mul]
        field_simp

/-- The sharp histogram bound: for an odd positive integer `t`, `n ≥ N_*`, `q ≤ 2 b_n` and
`y ∈ G_q`, `3^q Hg_{n,q}(y) < 𝓗_hist n^{5/2} 𝗀^{n/2}`. -/
theorem three_pow_mul_residueHistogram_lt_Hhist {t : ℤ} (hodd : Odd t) (ht : 0 < t) {n q : ℕ}
    (hn : generationThreshold ≤ n) (hq : q ≤ 2 * scale n) (y : ResidueGroup q) :
    (3 : ℝ) ^ q * residueHistogram t n q y <
      (Hhist : ℝ) * (n : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) := by
  have hH := three_pow_mul_residueHistogram_lt hodd ht hn hq y
  have hS := one_add_sum_cap_add_three_lt_sq_div_82 hn
  have hn1 : 1 ≤ n := le_trans (by rw [generationThreshold_def]; norm_num) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * √(n : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num,
      Real.rpow_add hn0, Real.rpow_natCast]
  have hg : (0 : ℝ) < (growthRatio : ℝ) ^ ((n : ℝ) / 2) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast growthRatio_pos
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hpos : (0 : ℝ) < 97 / 128 * 37170 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) := by
    positivity
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) := by
    positivity
  rw [hpow, Hhist_cast]
  calc (3 : ℝ) ^ q * residueHistogram t n q y
      < 97 / 128 * 37170 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) *
          ∑ j ∈ Finset.range n, ((cap j : ℝ) + 3) := hH
    _ ≤ 97 / 128 * 37170 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) *
          ((n : ℝ) ^ 2 / 82) := mul_le_mul_of_nonneg_left (by linarith) hpos.le
    _ = 1802745 / 5248 * ((n : ℝ) ^ 2 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2)) := by
        ring
    _ ≤ 344 * ((n : ℝ) ^ 2 * √(n : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hn2
    _ = 344 * ((n : ℝ) ^ 2 * √(n : ℝ)) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) := by ring

/-- **Sharp pairing estimate**. For an odd positive integer `t`, `n ≥ N_*`, `q ≤ 2 b_n`,
a set `𝓗' ⊆ 𝓗_n(t)` of central histories and `f : G_q → ℝ`,
`∑_{h ∈ 𝓗'} ω(h) |f(R_h mod 3^q)| ≤ 𝓗_hist n^{5/2} 𝗀^{n/2} ⟨|f|⟩_q`. -/
@[collatz_pos_dens "lem_pairing_sharp"]
theorem finsum_weight_mul_abs_le_Hhist {t : ℤ} (hodd : Odd t) (ht : 0 < t) {n q : ℕ}
    (hn : generationThreshold ≤ n) (hq : q ≤ 2 * scale n)
    {H' : Set (Fin n → Word)} (hH' : H' ⊆ centralHistories t n)
    (f : ResidueGroup q → ℝ) :
    ∑ᶠ h ∈ H', ((concatWord h).weight : ℝ) *
        |f ((historyEndpoint t h).num : ResidueGroup q)| ≤
      (Hhist : ℝ) * (n : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2) *
        residueAvg q (fun y => |f y|) :=
  finsum_weight_mul_abs_le_of_three_pow_mul_residueHistogram_le hodd ht
    (fun y => (three_pow_mul_residueHistogram_lt_Hhist hodd ht hn hq y).le) hH' f

end CollatzPosDens
