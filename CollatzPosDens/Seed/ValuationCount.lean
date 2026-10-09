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
public import CollatzPosDens.Seed.BlockValuationWindow
public import CollatzPosDens.Seed.Tuples

/-!
# Valuations at a fixed depth

Let `M` be a rational number, `n ≥ 8058` and `D` an integer. The valuation sums `A(h)` of the
central histories `h ∈ 𝓗_n(M)` of depth `D(h) = D` take fewer than `n² / 56` values.

Indeed, writing `h = (w₀, …, w_{n-1})`, each `w_j` lies in `𝒲(b_j, r_{b_j}, K_j)`, so with
`λ = log₂ 3` the valuation window gives
`2b_j + λ(|w_j| - b_j) - 1 < A(w_j) < 2b_j + λ(|w_j| - b_j) + 1 + K_j`. Summing over `j < n`,
using `A(h) = ∑ A(w_j)` and `D = ∑ |w_j|`, the integer `A(h)` lies in an open interval of
length `2n + K_*` depending only on `n` and `D`, where `K_* = ∑_{j<n} K_j ≤ 16n + n(n-1)/64`.
Hence there are at most `18n + n²/64 < n²/56` values.

## Main results

* `CollatzPosDens.centralHistories_valSum_atDepth_ncard_lt`: the set
  `{A(h) : h ∈ 𝓗_n(M), D(h) = D}` is finite with fewer than `n² / 56` elements.

## Implementation notes

The statement records finiteness explicitly, since `Set.ncard` of an infinite set is `0`. No
parity or positivity hypothesis on `M` is needed, and the bound `n ≥ 8058` is the one the final
inequality `18n + n²/64 < n²/56` uses.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The sum of the caps over the first `n` scales is at most `16n + n(n-1)/64`, in the cleared
form `64 ∑_{j<n} K_j ≤ 64 · 16 n + n(n-1)`. -/
theorem centralHistories_valSum_atDepth_capSum_le (n : ℕ) :
    64 * ∑ j ∈ Finset.range n, cap j ≤ 64 * 16 * n + n * (n - 1) := by
  have h1 : ∑ j ∈ Finset.range n, cap j = 16 * n + ∑ j ∈ Finset.range n, j / 32 := by
    simp [cap, Finset.sum_add_distrib, mul_comm]
  have h2 : 64 * ∑ j ∈ Finset.range n, j / 32 ≤ (∑ j ∈ Finset.range n, j) * 2 := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by omega
  rw [Finset.sum_range_id_mul_two] at h2
  rw [h1]
  omega

/-- **Valuations at a fixed depth.** For `n ≥ 8058` and an integer `D`, the valuation sums `A(h)`
of the central histories `h ∈ 𝓗_n(M)` of depth `D(h) = D` form a finite set with fewer than
`n² / 56` elements. -/
@[collatz_pos_dens "lem_s05_valuation_count"]
theorem centralHistories_valSum_atDepth_ncard_lt (M : ℚ) {n : ℕ} (hn : 8058 ≤ n) (D : ℤ) :
    {a : ℕ | ∃ h ∈ centralHistories M n, (historyDepth h : ℤ) = D ∧
        (concatWord h).valSum = a}.Finite ∧
      ({a : ℕ | ∃ h ∈ centralHistories M n, (historyDepth h : ℤ) = D ∧
        (concatWord h).valSum = a}.ncard : ℝ) < (n : ℝ) ^ 2 / 56 := by
  set S := {a : ℕ | ∃ h ∈ centralHistories M n, (historyDepth h : ℤ) = D ∧
    (concatWord h).valSum = a}
  set lam := Real.logb 2 3
  set Kst : ℕ := ∑ j ∈ Finset.range n, cap j
  set c : ℕ := 2 * n + Kst
  set L : ℝ := ∑ j ∈ Finset.range n, (2 * (scale j : ℝ) - scale j * lam) + D * lam - n
  have hnpos : 0 < n := by omega
  have hwin : ∀ a ∈ S, L < a ∧ (a : ℝ) < L + c := by
    rintro a ⟨h, hh, hD, rfl⟩
    have hw : ∀ j : Fin n, h j ∈ firstCrossing (scale j) (rb (scale j)) (cap j) := fun j =>
      centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily hh.1 j)
    have hA : ((concatWord h).valSum : ℝ) = ∑ j : Fin n, ((h j).valSum : ℝ) := by
      rw [valSum_concatWord]; push_cast; rfl
    have hDs : (D : ℝ) = ∑ j : Fin n, ((h j).length : ℝ) := by
      rw [← hD, historyDepth_eq_sum]; push_cast; rfl
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hnpos⟩⟩
    have hlo := Finset.sum_lt_sum_of_nonempty hne fun j _ =>
      (valSum_mem_window_of_mem_firstCrossing_rb (hw j)).1
    have hhi := Finset.sum_lt_sum_of_nonempty hne fun j _ =>
      (valSum_mem_window_of_mem_firstCrossing_rb (hw j)).2
    have e1 : ∑ j : Fin n, (2 * (scale j : ℝ) + ((h j).length - scale j) * lam - 1) =
        L := by
      simp only [L, hDs, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_mul]
      rw [Fin.sum_univ_eq_sum_range (fun j => 2 * (scale j : ℝ)),
        Fin.sum_univ_eq_sum_range (fun j => (scale j : ℝ) * lam)]
      ring
    have e2 : ∑ j : Fin n, (2 * (scale j : ℝ) + ((h j).length - scale j) * lam + 1 + cap j) =
        L + c := by
      simp only [L, c, Kst, hDs, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_mul]
      rw [Fin.sum_univ_eq_sum_range (fun j => 2 * (scale j : ℝ)),
        Fin.sum_univ_eq_sum_range (fun j => (scale j : ℝ) * lam),
        Fin.sum_univ_eq_sum_range (fun j => (cap j : ℝ))]
      push_cast
      ring
    rw [hA]
    exact ⟨e1 ▸ hlo, e2 ▸ hhi⟩
  set m : ℤ := ⌊L⌋ + 1
  have hsub : (fun a : ℕ => (a : ℤ)) '' S ⊆ ↑(Finset.Ico m (m + c)) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := hwin a ha
    simp only [Finset.coe_Ico, Set.mem_Ico, m]
    refine ⟨Int.add_one_le_of_lt (Int.floor_lt.2 (by exact_mod_cast h1)), ?_⟩
    exact_mod_cast (by linarith [Int.lt_floor_add_one L] : (a : ℝ) < ⌊L⌋ + 1 + c)
  have hinj : Set.InjOn (fun a : ℕ => (a : ℤ)) S := fun _ _ _ _ h => Int.ofNat_inj.mp h
  have hfin : S.Finite :=
    (Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hsub) hinj)
  refine ⟨hfin, ?_⟩
  have hcard : S.ncard ≤ c := by
    rw [← hinj.ncard_image]
    calc ((fun a : ℕ => (a : ℤ)) '' S).ncard ≤ (↑(Finset.Ico m (m + c)) : Set ℤ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = c := by rw [Set.ncard_coe_finset, Int.card_Ico]; simp
  have hK : 64 * Kst ≤ 64 * 16 * n + n * (n - 1) := centralHistories_valSum_atDepth_capSum_le n
  have hc : 56 * c < n ^ 2 := by
    have : 64 * 56 * c ≤ 64 * 56 * 2 * n + 56 * (64 * 16 * n + n * (n - 1)) := by
      simp only [c]; linarith
    have h' : n * (n - 1) + n = n * n := by
      cases n with
      | zero => omega
      | succ k => simp [Nat.mul_succ]
    nlinarith
  have : (56 : ℝ) * S.ncard < (n : ℝ) ^ 2 := by
    exact_mod_cast (show 56 * S.ncard < n ^ 2 by omega)
  linarith

end CollatzPosDens
