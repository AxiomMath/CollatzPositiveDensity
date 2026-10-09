/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Seed.Histogram
public import CollatzPosDens.Seed.HistogramBound
public import CollatzPosDens.Seed.History
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# The pairing estimate

Let `M` be an odd positive integer, `n ≥ 10000` and `q ≤ 2 * scale n`, let
`𝓗' ⊆ centralHistories M n` and let `f : ResidueGroup q → ℝ`. Writing `ω(h)` for the weight of
the concatenated word of `h`, `R_h` for `historyEndpoint M h`, `𝖦` for `histogramGrowth` and
`⟨|f|⟩_q` for `residueAvg q |f|`,
$$\sum_{h ∈ 𝓗'} ω(h)\,|f(R_h \bmod 3^q)| \le
  \frac{4075}{56}\cdot\frac{277}{128}\, n^{5/2}\, \mathsf G^n\, ⟨|f|⟩_q.$$
Grouping the histories by the residue `y = R_h mod 3^q` bounds the left side by
`∑_y Hg(y) |f(y)| ≤ max_y (3^q Hg(y)) ⟨|f|⟩_q`, where `Hg = residueHistogram M n q`, and
`three_pow_mul_residueHistogram_lt` bounds `3^q Hg(y)`.

## Main results

* `CollatzPosDens.pairing_finsum_weight_mul_abs_le`: the pairing estimate.
* `CollatzPosDens.pairing_finsum_weight_mul_abs_le_endpoint_eq_int`: the endpoint of a
  central history from a positive odd integer is an integer.

## Implementation notes

The endpoint `R_h` is a rational number, an integer for `h ∈ centralHistories M n` since the
concatenated word is admissible from `M`; as in `CollatzPosDens.weightedCentralSum`, its residue
modulo `3^q` is taken to be that of its numerator. The sum over `𝓗'` is a `finsum` over a set,
finite since `centralHistories M n` is. The power `n^{5/2}` is the real power
`(n : ℝ) ^ (5 / 2 : ℝ)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The endpoint of a central history from a positive odd integer `M` is an integer. -/
theorem pairing_finsum_weight_mul_abs_le_endpoint_eq_int {M : ℤ} (hodd : Odd M) (hM : 0 < M)
    {n : ℕ} {h : Fin n → Word} (hh : h ∈ centralHistories M n) :
    ∃ m : ℤ, historyEndpoint M h = m := by
  have hsrc : historyEndpoint M h = src (concatWord h) M := by
    rw [historyEndpoint, historyEndpointAt_eq_src_concatWord M h le_rfl]
    rfl
  obtain ⟨m, hm, -⟩ := hh.2.exists_src_eq_pos_odd hM hodd
  exact ⟨m, hsrc.trans hm⟩

/-- **Pairing estimate**. For an odd positive integer `M`, `n ≥ 10000`, `q ≤ 2 * scale n`, a
set `H' ⊆ centralHistories M n` and `f : ResidueGroup q → ℝ`, the sum over `h ∈ H'` of the
weight of `concatWord h` times `|f|` at the residue of `historyEndpoint M h` is at most
`(4075/56)(277/128) n^{5/2} histogramGrowth^n` times `residueAvg q |f|`. -/
@[collatz_pos_dens "lem_pairing"]
theorem pairing_finsum_weight_mul_abs_le {M : ℤ} (hodd : Odd M) (hM : 0 < M) {n q : ℕ}
    (hn : 10000 ≤ n) (hq : q ≤ 2 * scale n)
    {H' : Set (Fin n → Word)} (hH' : H' ⊆ centralHistories M n) (f : ResidueGroup q → ℝ) :
    ∑ᶠ h ∈ H', ((concatWord h).weight : ℝ) *
        |f ((historyEndpoint M h).num : ResidueGroup q)| ≤
      4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n *
        residueAvg q (fun y => |f y|) := by
  classical
  set C : ℝ := 4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n
  have hfin : H'.Finite := (centralHistories_finite M n).subset hH'
  set s := hfin.toFinset
  set r : (Fin n → Word) → ResidueGroup q := fun h => ((historyEndpoint M h).num : ResidueGroup q)
  have h3 : (0 : ℝ) < 3 ^ q := by positivity
  have hclass : ∀ y, ∑ h ∈ s with r h = y, ((concatWord h).weight : ℝ) ≤ C / 3 ^ q := by
    intro y
    set S : Set (Fin n → Word) := {h | h ∈ centralHistories M n ∧
        ∃ m : ℤ, (m : ℚ) = historyEndpoint M h ∧ (m : ResidueGroup q) = y}
    have hSfin : S.Finite :=
      (centralHistories_finite M n).subset fun h hh => hh.1
    have hHg : residueHistogram M n q y = ∑ h ∈ hSfin.toFinset, ((concatWord h).weight : ℝ) :=
      finsum_mem_eq_finite_toFinset_sum _ hSfin
    have hsub : s.filter (fun h => r h = y) ⊆ hSfin.toFinset := by
      intro h hh
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hh
      obtain ⟨hh, hry⟩ := hh
      have hc := hH' hh
      obtain ⟨m, hm⟩ := pairing_finsum_weight_mul_abs_le_endpoint_eq_int hodd hM hc
      rw [Set.Finite.mem_toFinset]
      refine ⟨hc, m, hm.symm, ?_⟩
      have : (historyEndpoint M h).num = m := by
        rw [hm, Rat.num_intCast]
      simpa [r, this] using hry
    calc ∑ h ∈ s with r h = y, ((concatWord h).weight : ℝ)
        ≤ ∑ h ∈ hSfin.toFinset, ((concatWord h).weight : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by
            exact_mod_cast (Word.weight_pos _).le
      _ = residueHistogram M n q y := hHg.symm
      _ ≤ C / 3 ^ q := by
          rw [le_div_iff₀ h3, mul_comm]
          exact (three_pow_mul_residueHistogram_lt hodd hM hn hq y).le
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

end CollatzPosDens
