/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Int.Interval
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05BlockValuationWindow
public import CollatzPosDens.Seed.S05Tuples

/-!
# Valuations at a fixed depth

Let `t` be a starting point, `n ≥ 1` and `D` an integer. The valuation sums `A(h)` of the
central histories `h ∈ 𝓗_n(t)` of depth `D(h) = D` take at most `∑_{j<n} (K_j + 3)` values.

Writing `h = (w_0, …, w_{n-1})`, each `w_j` lies in `𝒞(b_j, K_j) ⊆ 𝒲(b_j, r_{b_j}, K_j)`, so
with `λ = log₂ 3` the valuation window gives
`2b_j + λ(|w_j| - b_j) - 1 < A(w_j) < 2b_j + λ(|w_j| - b_j) + 1 + K_j`. Summing over
`0 ≤ j < n`, using `A(h) = ∑ A(w_j)` and `D = ∑ |w_j|`, the integer `A(h)` lies in an open
interval of length `2n + ∑_{j<n} K_j` depending only on `n` and `D`, which contains at most that
many integers; and this length is at most `∑_{j<n} (K_j + 3)`.

## Main results

* `CollatzPosDens.valSum_concatWord_atDepth_ncard_le`: for any family of nonempty tuples
  `(w_0, …, w_{m-1})` with `w_k ∈ 𝒲(b_k, r_{b_k}, K_k)`, the valuation sums at a fixed depth
  form a finite set with at most `2m + ∑_{k<m} K_k` elements.
* `CollatzPosDens.centralHistories_valSum_atDepth_ncard_le`: the set
  `{A(h) : h ∈ 𝓗_n(t), D(h) = D}` is finite with at most `∑_{j<n} (K_j + 3)` elements.

## Implementation notes

The statement records finiteness explicitly, since `Set.ncard` of an infinite set is `0`. The
hypotheses that `t` is odd and positive are not needed and are dropped.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Counting valuation sums in a window.** Let `m ≥ 1` and let `T` be a set of tuples
`(w_0, …, w_{m-1})` of words with `w_k ∈ 𝒲(b_k, r_{b_k}, K_k)` for every `k`. For an integer
`D`, the valuation sums `A(ŵ)` of the tuples of `T` of total length `D` form a finite set with at
most `2m + ∑_{k<m} K_k` elements. -/
theorem valSum_concatWord_atDepth_ncard_le {m : ℕ} (hm : 0 < m) (b K : ℕ → ℕ)
    {T : Set (Fin m → Word)}
    (hT : ∀ h ∈ T, ∀ k : Fin m, h k ∈ firstCrossing (b k) (rb (b k)) (K k)) (D : ℤ) :
    {a : ℕ | ∃ h ∈ T, ((concatWord h).length : ℤ) = D ∧ (concatWord h).valSum = a}.Finite ∧
      {a : ℕ | ∃ h ∈ T, ((concatWord h).length : ℤ) = D ∧
        (concatWord h).valSum = a}.ncard ≤ 2 * m + ∑ k ∈ Finset.range m, K k := by
  set S := {a : ℕ | ∃ h ∈ T, ((concatWord h).length : ℤ) = D ∧ (concatWord h).valSum = a}
  set lam := Real.logb 2 3
  set c : ℕ := 2 * m + ∑ k ∈ Finset.range m, K k
  set L : ℝ := ∑ k ∈ Finset.range m, (2 * (b k : ℝ) - b k * lam) + D * lam - m
  have hwin : ∀ a ∈ S, L < a ∧ (a : ℝ) < L + c := by
    rintro a ⟨h, hh, hD, rfl⟩
    have hw := hT h hh
    have hA : ((concatWord h).valSum : ℝ) = ∑ k : Fin m, ((h k).valSum : ℝ) := by
      rw [valSum_concatWord]; push_cast; rfl
    have hDs : (D : ℝ) = ∑ k : Fin m, ((h k).length : ℝ) := by
      rw [← hD, length_concatWord]; push_cast; rfl
    have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hm⟩⟩
    have hlo := Finset.sum_lt_sum_of_nonempty hne fun k _ =>
      (valSum_mem_window_of_mem_firstCrossing_rb (hw k)).1
    have hhi := Finset.sum_lt_sum_of_nonempty hne fun k _ =>
      (valSum_mem_window_of_mem_firstCrossing_rb (hw k)).2
    have e1 : ∑ k : Fin m, (2 * (b k : ℝ) + ((h k).length - b k) * lam - 1) = L := by
      simp only [L, hDs, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_mul]
      rw [Fin.sum_univ_eq_sum_range (fun k => 2 * (b k : ℝ)),
        Fin.sum_univ_eq_sum_range (fun k => (b k : ℝ) * lam)]
      ring
    have e2 : ∑ k : Fin m, (2 * (b k : ℝ) + ((h k).length - b k) * lam + 1 + K k) =
        L + c := by
      simp only [L, c, hDs, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_mul]
      rw [Fin.sum_univ_eq_sum_range (fun k => 2 * (b k : ℝ)),
        Fin.sum_univ_eq_sum_range (fun k => (b k : ℝ) * lam),
        Fin.sum_univ_eq_sum_range (fun k => (K k : ℝ))]
      push_cast
      ring
    rw [hA]
    exact ⟨e1 ▸ hlo, e2 ▸ hhi⟩
  set n₀ : ℤ := ⌊L⌋ + 1
  have hsub : (fun a : ℕ => (a : ℤ)) '' S ⊆ ↑(Finset.Ico n₀ (n₀ + c)) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := hwin a ha
    simp only [Finset.coe_Ico, Set.mem_Ico, n₀]
    refine ⟨Int.add_one_le_of_lt (Int.floor_lt.2 (by exact_mod_cast h1)), ?_⟩
    exact_mod_cast (by linarith [Int.lt_floor_add_one L] : (a : ℝ) < ⌊L⌋ + 1 + c)
  have hinj : Set.InjOn (fun a : ℕ => (a : ℤ)) S := fun _ _ _ _ h => Int.ofNat_inj.mp h
  refine ⟨Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hsub) hinj, ?_⟩
  rw [← hinj.ncard_image]
  calc ((fun a : ℕ => (a : ℤ)) '' S).ncard ≤ (↑(Finset.Ico n₀ (n₀ + c)) : Set ℤ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = c := by rw [Set.ncard_coe_finset, Int.card_Ico]; simp

/-- **Valuations at a fixed depth.** For `n ≥ 1` and an integer `D`, the valuation sums `A(h)`
of the central histories `h ∈ 𝓗_n(t)` of depth `D(h) = D` form a finite set with at most
`∑_{j<n} (K_j + 3)` elements. -/
@[collatz_pos_dens "lem_s05_valuation_count"]
theorem centralHistories_valSum_atDepth_ncard_le (t : ℚ) {n : ℕ} (hn : 1 ≤ n) (D : ℤ) :
    {a : ℕ | ∃ h ∈ centralHistories t n, (historyDepth h : ℤ) = D ∧
        (concatWord h).valSum = a}.Finite ∧
      {a : ℕ | ∃ h ∈ centralHistories t n, (historyDepth h : ℤ) = D ∧
        (concatWord h).valSum = a}.ncard ≤ ∑ j ∈ Finset.range n, (cap j + 3) := by
  have hm : 0 < n := hn
  have hT : ∀ h ∈ centralHistories t n, ∀ k : Fin n,
      h k ∈ firstCrossing (scale k) (rb (scale k)) (cap k) := fun h hh k =>
    centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily hh.1 k)
  obtain ⟨hfin, hcard⟩ := valSum_concatWord_atDepth_ncard_le hm scale cap hT D
  refine ⟨hfin, hcard.trans ?_⟩
  have h3 : ∑ j ∈ Finset.range n, (cap j + 3) = ∑ j ∈ Finset.range n, cap j + 3 * n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  omega

end CollatzPosDens
