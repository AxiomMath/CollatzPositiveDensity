/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import CollatzPosDens.Attr

/-!
# Packing of a unimodal sequence

Let `a : ℤ → ℝ` be nonnegative with finite support, and *unimodal* in the sense that every
superlevel set `{x | λ ≤ a x}` with `λ > 0` is a set of consecutive integers. If `Z ⊆ ℤ` is
`ρ`-separated, i.e. `ρ ≤ |z - z'|` for distinct `z, z' ∈ Z`, then
$$\sum_{z\in Z} a(z) \le \max_x a(x) + \rho^{-1}\sum_{x\in\mathbb Z} a(x).$$

The proof is the layer-cake decomposition of `a`: peeling off the smallest positive value `m`
of `a` on its support `I` (a set of `k` consecutive integers) leaves a sequence of the same kind
with smaller support, while `Z` meets `I` in at most `1 + k / ρ` points.

## Main results

* `CollatzPosDens.rnUnimodalPack_finset_le`: the inequality for a finite separated
  set `T`, a finset `s` containing the support, and any nonnegative upper bound `M` of `a`.
* `CollatzPosDens.rnUnimodalPack`: the statement with `∑ᶠ`, `⨆` and a
  set `Z`.

## Implementation notes

The layer-cake decomposition is carried out as an induction on the size of a finset containing
the support: one subtracts the least positive value `m` from `a` (truncating at `0`). The bound
is proved for an arbitrary nonnegative upper bound `M` of `a` in place of `max a`, which makes
the induction step immediate (`M - m` bounds the truncated sequence); `max a` is then
`⨆ x, a x`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- A `ρ`-separated nonempty finset of integers lying in `[lo, hi]` has at most
`1 + (hi - lo) / ρ` elements, in the form `(#S - 1) ρ ≤ hi - lo`. -/
private theorem card_sub_one_mul_le (ρ : ℝ) (S : Finset ℤ)
    (hsep : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → ρ ≤ |(z : ℝ) - z'|) (lo : ℝ) (hlo : ∀ x ∈ S, lo ≤ x)
    (hi : ℝ) (hhi : ∀ x ∈ S, (x : ℝ) ≤ hi) (hne : S.Nonempty) :
    ((S.card : ℝ) - 1) * ρ ≤ hi - lo := by
  induction S using Finset.induction_on_max generalizing hi with
  | empty => simp at hne
  | insert m S hlt ih =>
    have hmS : m ∉ S := fun h => lt_irrefl _ (hlt m h)
    rw [Finset.card_insert_of_notMem hmS]
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp only [card_empty, zero_add, Nat.cast_one, sub_self, zero_mul, sub_nonneg]
      linarith [hlo m (by simp), hhi m (by simp)]
    · have hb : ∀ x ∈ S, (x : ℝ) ≤ hi - ρ := by
        intro x hx
        have h₁ := hsep m (by simp) x (by simp [hx]) (fun h => lt_irrefl _ (h ▸ hlt x hx))
        have h₂ : (x : ℝ) < m := by exact_mod_cast hlt x hx
        rw [abs_of_pos (by linarith)] at h₁
        linarith [hhi m (by simp)]
      have := ih (fun z hz z' hz' h => hsep z (by simp [hz]) z' (by simp [hz']) h)
        (fun x hx => hlo x (by simp [hx])) (hi - ρ) hb hS
      push_cast
      linarith

/-- A `ρ`-separated finset `S` of integers, each of whose intervals `[x, y]` (`x, y ∈ S`) lies
in the finset `K`, has at most `1 + #K / ρ` elements. -/
theorem card_le_one_add_card_div {ρ : ℝ} (hρ : 0 < ρ) (S K : Finset ℤ)
    (hsep : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → ρ ≤ |(z : ℝ) - z'|)
    (hK : ∀ x ∈ S, ∀ y ∈ S, Finset.Icc x y ⊆ K) :
    (S.card : ℝ) ≤ 1 + K.card / ρ := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp only [card_empty, Nat.cast_zero]
    positivity
  have h₁ := card_sub_one_mul_le ρ S hsep (S.min' hSne)
    (fun x hx => by exact_mod_cast S.min'_le x hx) (S.max' hSne)
    (fun x hx => by exact_mod_cast S.le_max' x hx) hSne
  have h₂ := Finset.card_le_card (hK _ (S.min'_mem hSne) _ (S.max'_mem hSne))
  rw [Int.card_Icc] at h₂
  have h₃ : ((S.max' hSne : ℤ) : ℝ) - (S.min' hSne : ℤ) + 1 ≤ K.card := by
    have : S.max' hSne - S.min' hSne + 1 ≤ (K.card : ℤ) := by omega
    exact_mod_cast this
  linarith [(le_div_iff₀ hρ).2 (show ((S.card : ℝ) - 1) * ρ ≤ K.card by linarith)]

/-- Truncating `a` at level `m ≥ 0` keeps every positive superlevel set order-connected. -/
theorem ordConnected_setOf_le_max_sub {a : ℤ → ℝ}
    (huni : ∀ l : ℝ, 0 < l → {x : ℤ | l ≤ a x}.OrdConnected) {m : ℝ} (hm : 0 ≤ m) (l : ℝ)
    (hl : 0 < l) : {x : ℤ | l ≤ max (a x - m) 0}.OrdConnected := by
  have : {x : ℤ | l ≤ max (a x - m) 0} = {x : ℤ | l + m ≤ a x} := by
    ext x
    simp only [Set.mem_ofPred_eq, le_max_iff]
    exact ⟨by rintro (h | h) <;> linarith, fun h => Or.inl (by linarith)⟩
  rw [this]
  exact huni _ (by linarith)

/-- If every value of `a` is `0` or at least `m > 0`, the sum of `a` splits as the sum of its
truncation at `m` plus `m` times the size of the superlevel set `{m ≤ a}`. -/
theorem sum_eq_sum_max_sub_add_mul_card {a : ℤ → ℝ} {m : ℝ} (hm0 : 0 < m)
    (hdich : ∀ x, a x = 0 ∨ m ≤ a x) (u : Finset ℤ) :
    ∑ x ∈ u, a x = ∑ x ∈ u, max (a x - m) 0 + m * (u.filter (fun x => m ≤ a x)).card := by
  have hdecomp : ∀ x, a x = max (a x - m) 0 + m * (if m ≤ a x then 1 else 0) := by
    intro x
    rcases hdich x with h | h
    · simp [h, not_le.mpr hm0, hm0.le]
    · simp [h]
  rw [Finset.sum_congr rfl (fun x _ => hdecomp x), Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_boole]

/-- **Packing of a unimodal sequence**, finset form with an arbitrary upper bound. Let
`a : ℤ → ℝ` be nonnegative, supported in the finset `s`, with every superlevel set
`{x | λ ≤ a x}` (`λ > 0`) order-connected, and let `M` bound `a`. Then for every
`ρ`-separated finset `T`, `∑ z ∈ T, a z ≤ M + ρ⁻¹ * ∑ x ∈ s, a x`. -/
theorem rnUnimodalPack_finset_le {ρ : ℝ} (hρ : 0 < ρ) (T : Finset ℤ)
    (hsep : ∀ z ∈ T, ∀ z' ∈ T, z ≠ z' → ρ ≤ |(z : ℝ) - z'|) (s : Finset ℤ) (a : ℤ → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hsupp : ∀ x, a x ≠ 0 → x ∈ s)
    (huni : ∀ l : ℝ, 0 < l → {x : ℤ | l ≤ a x}.OrdConnected) (M : ℝ)
    (hM : ∀ x, a x ≤ M) :
    ∑ z ∈ T, a z ≤ M + ρ⁻¹ * ∑ x ∈ s, a x := by
  classical
  induction s using Finset.strongInduction generalizing a M with
  | H s ih =>
  by_cases hpos : (s.filter (fun x => 0 < a x)).Nonempty
  swap
  · have h0 : ∀ x, a x = 0 := by
      intro x
      by_contra hx
      exact hpos ⟨x, by simp [hsupp x hx, lt_of_le_of_ne (ha x) (Ne.symm hx)]⟩
    simp [h0, (ha 0).trans (hM 0)]
  obtain ⟨x0, hx0, hmin⟩ := (s.filter (fun x => 0 < a x)).exists_min_image a hpos
  simp only [Finset.mem_filter] at hx0
  set m := a x0 with hm
  have hm0 : 0 < m := hx0.2
  have hdich : ∀ x, a x = 0 ∨ m ≤ a x := by
    intro x
    rcases (ha x).eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hmin x (by simp [hsupp x h.ne', h]))
  set a' : ℤ → ℝ := fun x => max (a x - m) 0 with ha'
  have hIH := ih (s.erase x0) (Finset.erase_ssubset hx0.1) a' (fun x => le_max_right _ _)
    (by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · rintro rfl
        simp [ha'] at hx
        linarith [hm]
      · exact hsupp x fun h => by simp [ha', h, hm0.le] at hx)
    (ordConnected_setOf_le_max_sub huni hm0.le)
    (M - m) (fun x => by
      simp only [ha', max_le_iff]
      exact ⟨by linarith [hM x], by linarith [hM x0]⟩)
  rw [Finset.sum_erase s (show a' x0 = 0 by simp [ha', hm])] at hIH
  set S := T.filter (fun x => m ≤ a x)
  set K := s.filter (fun x => m ≤ a x)
  have hcount : (S.card : ℝ) ≤ 1 + K.card / ρ := by
    refine card_le_one_add_card_div hρ S K
      (fun z hz z' hz' h => hsep z (mem_filter.mp hz).1 z' (mem_filter.mp hz').1 h) ?_
    intro y hy y' hy' x hx
    have hx' : m ≤ a x := (huni m hm0).out (mem_filter.mp hy).2 (mem_filter.mp hy').2
      (Finset.mem_Icc.mp hx)
    exact mem_filter.mpr ⟨hsupp x (by linarith), hx'⟩
  rw [sum_eq_sum_max_sub_add_mul_card hm0 hdich T, sum_eq_sum_max_sub_add_mul_card hm0 hdich s]
  calc ∑ z ∈ T, a' z + m * S.card ≤ (M - m + ρ⁻¹ * ∑ x ∈ s, a' x) + m * (1 + K.card / ρ) := by
        gcongr
    _ = M + ρ⁻¹ * (∑ x ∈ s, a' x + m * K.card) := by
        rw [div_eq_mul_inv]
        ring

/-- **Packing of a unimodal sequence.** Let `a : ℤ → ℝ` be
nonnegative with finite support, such that for every real `λ > 0` the set `{x | λ ≤ a x}`
consists of consecutive integers. Let `ρ > 0` and let `Z ⊆ ℤ` satisfy `ρ ≤ |z - z'|` for all
distinct `z, z' ∈ Z`. Then `∑_{z ∈ Z} a z ≤ max a + ρ⁻¹ ∑_{x ∈ ℤ} a x`. -/
@[collatz_pos_dens "lem_rn_unimodal_pack"]
theorem rnUnimodalPack (a : ℤ → ℝ) (ha : ∀ x, 0 ≤ a x) (hfin : (Function.support a).Finite)
    (huni : ∀ l : ℝ, 0 < l → {x : ℤ | l ≤ a x}.OrdConnected) {ρ : ℝ} (hρ : 0 < ρ)
    (Z : Set ℤ) (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → ρ ≤ |(z : ℝ) - z'|) :
    ∑ᶠ z ∈ Z, a z ≤ (⨆ x, a x) + ρ⁻¹ * ∑ᶠ x, a x := by
  classical
  set s := hfin.toFinset with hs
  have hsupp : ∀ x, a x ≠ 0 → x ∈ s := fun x hx => by simpa [hs] using hx
  have hbdd : BddAbove (Set.range a) := by
    refine ⟨∑ x ∈ s, a x, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : a x = 0
    · rw [hx]
      exact Finset.sum_nonneg (fun y _ => ha y)
    · exact Finset.single_le_sum (fun y _ => ha y) (hsupp x hx)
  have hM : ∀ x, a x ≤ ⨆ x, a x := fun x => le_ciSup hbdd x
  set T := s.filter (· ∈ Z) with hT
  have hZ : ∑ᶠ z ∈ Z, a z = ∑ z ∈ T, a z := by
    rw [← finsum_mem_inter_support, ← finsum_mem_coe_finset]
    congr 1
    ext x
    simp [hT, hs, and_comm]
  have hS : ∑ᶠ x, a x = ∑ x ∈ s, a x :=
    finsum_eq_sum_of_support_subset a hsupp
  rw [hZ, hS]
  exact rnUnimodalPack_finset_le hρ T
    (fun z hz z' hz' h => hsep z (Finset.mem_filter.mp hz).2 z' (Finset.mem_filter.mp hz').2 h)
    s a ha hsupp huni _ hM

end CollatzPosDens
