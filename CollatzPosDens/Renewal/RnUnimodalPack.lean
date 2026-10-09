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

* `CollatzPosDens.sum_le_add_inv_mul_sum_of_unimodal`: the inequality for a finite separated
  set `T`, a finset `s` containing the support, and any nonnegative upper bound `M` of `a`.
* `CollatzPosDens.finsum_mem_le_iSup_add_inv_mul_finsum`: the statement with `∑ᶠ`, `⨆` and a
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
    · have := hlo m (by simp)
      have := hhi m (by simp)
      simp
      linarith
    · have hsep' : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → ρ ≤ |(z : ℝ) - z'| := fun z hz z' hz' h =>
        hsep z (by simp [hz]) z' (by simp [hz']) h
      have hb : ∀ x ∈ S, (x : ℝ) ≤ hi - ρ := by
        intro x hx
        have h1 := hsep m (by simp) x (by simp [hx]) (fun h => lt_irrefl _ (h ▸ hlt x hx))
        have h2 : (x : ℝ) < m := by exact_mod_cast hlt x hx
        have h3 := hhi m (by simp)
        rw [abs_of_pos (by linarith)] at h1
        linarith
      have := ih hsep' (fun x hx => hlo x (by simp [hx])) (hi - ρ) hb hS
      push_cast
      linarith

/-- A `ρ`-separated finset `T` meets an order-connected superlevel set `{x | m ≤ a x}`
(`m > 0`) of a sequence supported in `s` in at most `1 + #{x ∈ s | m ≤ a x} / ρ` points. -/
theorem card_filter_le_one_add_card_div {ρ : ℝ} (hρ : 0 < ρ) (T s : Finset ℤ)
    (hsep : ∀ z ∈ T, ∀ z' ∈ T, z ≠ z' → ρ ≤ |(z : ℝ) - z'|) (a : ℤ → ℝ) {m : ℝ} (hm0 : 0 < m)
    (hsupp : ∀ x, a x ≠ 0 → x ∈ s) (huni : {x : ℤ | m ≤ a x}.OrdConnected) :
    ((T.filter (fun x => m ≤ a x)).card : ℝ) ≤ 1 + (s.filter (fun x => m ≤ a x)).card / ρ := by
  set S := T.filter (fun x => m ≤ a x)
  set K := s.filter (fun x => m ≤ a x)
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.card_empty, Nat.cast_zero]
    positivity
  have hsepS : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → ρ ≤ |(z : ℝ) - z'| := fun z hz z' hz' h =>
    hsep z (Finset.mem_filter.mp hz).1 z' (Finset.mem_filter.mp hz').1 h
  have h1 := card_sub_one_mul_le ρ S hsepS (S.min' hSne)
    (fun x hx => by exact_mod_cast S.min'_le x hx) (S.max' hSne)
    (fun x hx => by exact_mod_cast S.le_max' x hx) hSne
  have hsub : Finset.Icc (S.min' hSne) (S.max' hSne) ⊆ K := by
    intro x hx
    have hmn := (Finset.mem_filter.mp (S.min'_mem hSne)).2
    have hmx := (Finset.mem_filter.mp (S.max'_mem hSne)).2
    have hx' : m ≤ a x :=
      huni.out (show S.min' hSne ∈ {x : ℤ | m ≤ a x} from hmn)
        (show S.max' hSne ∈ {x : ℤ | m ≤ a x} from hmx) (Finset.mem_Icc.mp hx)
    have : a x ≠ 0 := by linarith
    exact Finset.mem_filter.mpr ⟨hsupp x this, hx'⟩
  have h2 := Finset.card_le_card hsub
  rw [Int.card_Icc] at h2
  have h3 : ((S.max' hSne : ℤ) : ℝ) - (S.min' hSne : ℤ) + 1 ≤ K.card := by
    have hle : S.min' hSne ≤ S.max' hSne := S.min'_le_max' hSne
    have : ((S.max' hSne + 1 - S.min' hSne : ℤ)) ≤ (K.card : ℤ) := by
      have := Int.toNat_of_nonneg (show (0:ℤ) ≤ S.max' hSne + 1 - S.min' hSne by omega)
      omega
    have h4 : ((S.max' hSne + 1 - S.min' hSne : ℤ) : ℝ) ≤ ((K.card : ℤ) : ℝ) := by
      exact_mod_cast this
    push_cast at h4
    linarith
  have := (le_div_iff₀ hρ).mpr (show ((S.card : ℝ) - 1) * ρ ≤ K.card by linarith)
  linarith

/-- Truncating a sequence with order-connected positive superlevel sets from below by `m ≥ 0`,
`x ↦ max (a x - m) 0`, keeps its positive superlevel sets order-connected. -/
theorem ordConnected_setOf_le_max_sub {a : ℤ → ℝ} {m : ℝ} (hm0 : 0 ≤ m)
    (huni : ∀ l : ℝ, 0 < l → {x : ℤ | l ≤ a x}.OrdConnected) (l : ℝ) (hl : 0 < l) :
    {x : ℤ | l ≤ max (a x - m) 0}.OrdConnected := by
  have : {x : ℤ | l ≤ max (a x - m) 0} = {x : ℤ | l + m ≤ a x} := by
    ext x
    simp only [Set.mem_ofPred_eq, le_max_iff]
    constructor
    · rintro (h | h) <;> linarith
    · exact fun h => Or.inl (by linarith)
  rw [this]
  exact huni _ (by linarith)

/-- **Packing of a unimodal sequence**, finset form with an arbitrary upper bound. Let
`a : ℤ → ℝ` be nonnegative, supported in the finset `s`, with every superlevel set
`{x | λ ≤ a x}` (`λ > 0`) order-connected, and let `M ≥ 0` bound `a`. Then for every
`ρ`-separated finset `T`, `∑ z ∈ T, a z ≤ M + ρ⁻¹ * ∑ x ∈ s, a x`. -/
theorem sum_le_add_inv_mul_sum_of_unimodal {ρ : ℝ} (hρ : 0 < ρ) (T : Finset ℤ)
    (hsep : ∀ z ∈ T, ∀ z' ∈ T, z ≠ z' → ρ ≤ |(z : ℝ) - z'|) (s : Finset ℤ) (a : ℤ → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hsupp : ∀ x, a x ≠ 0 → x ∈ s)
    (huni : ∀ l : ℝ, 0 < l → {x : ℤ | l ≤ a x}.OrdConnected) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x, a x ≤ M) :
    ∑ z ∈ T, a z ≤ M + ρ⁻¹ * ∑ x ∈ s, a x := by
  classical
  induction s using Finset.strongInduction generalizing a M with
  | H s ih =>
  by_cases hpos : (s.filter (fun x => 0 < a x)).Nonempty
  swap
  · have h0 : ∀ x, a x = 0 := fun x => by
      by_contra hx
      exact hpos ⟨x, by simp [hsupp x hx, lt_of_le_of_ne (ha x) (Ne.symm hx)]⟩
    simp [h0, hM0]
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
  have hdecomp : ∀ x, a x = a' x + m * (if m ≤ a x then 1 else 0) := by
    intro x
    rcases hdich x with h | h
    · have h' : ¬ m ≤ 0 := not_le.mpr hm0
      simp [ha', h, h', hm0.le]
    · simp [ha', h]
  have hIH := ih (s.erase x0) (Finset.erase_ssubset hx0.1) a' (fun x => le_max_right _ _)
    (by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · rintro rfl
        simp [ha'] at hx
        linarith [hm]
      · by_contra hxs
        have : a x = 0 := by by_contra h; exact hxs (hsupp x h)
        simp [ha', this, hm0.le] at hx)
    (ordConnected_setOf_le_max_sub hm0.le huni) (M - m) (by linarith [hM x0]) (fun x => by
      simp only [ha', max_le_iff]
      exact ⟨by linarith [hM x], by linarith [hM x0]⟩)
  have ha'x0 : a' x0 = 0 := by simp [ha', hm]
  have hsum' : ∑ x ∈ s.erase x0, a' x = ∑ x ∈ s, a' x := by
    rw [← Finset.add_sum_erase s a' hx0.1, ha'x0, zero_add]
  rw [hsum'] at hIH
  have hcount := card_filter_le_one_add_card_div hρ T s hsep a hm0 hsupp (huni m hm0)
  set S := T.filter (fun x => m ≤ a x) with hS
  set K := s.filter (fun x => m ≤ a x) with hK
  have hsumT : ∑ z ∈ T, a z = ∑ z ∈ T, a' z + m * S.card := by
    rw [Finset.sum_congr rfl (fun x _ => hdecomp x), Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_boole, hS]
  have hsums : ∑ x ∈ s, a x = ∑ x ∈ s, a' x + m * K.card := by
    rw [Finset.sum_congr rfl (fun x _ => hdecomp x), Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_boole, hK]
  rw [hsumT, hsums]
  have hρinv : 0 < ρ⁻¹ := inv_pos.mpr hρ
  calc ∑ z ∈ T, a' z + m * S.card ≤ (M - m + ρ⁻¹ * ∑ x ∈ s, a' x) + m * (1 + K.card / ρ) := by
        gcongr
    _ = M + ρ⁻¹ * (∑ x ∈ s, a' x + m * K.card) := by ring

/-- **Packing of a unimodal sequence**. Let `a : ℤ → ℝ` be nonnegative with finite support, such
that for every real `λ > 0` the set `{x | λ ≤ a x}` consists of consecutive integers. Let `ρ > 0`
and let `Z ⊆ ℤ` satisfy `ρ ≤ |z - z'|` for all distinct `z, z' ∈ Z`. Then
`∑_{z ∈ Z} a z ≤ max a + ρ⁻¹ ∑_{x ∈ ℤ} a x`. -/
@[collatz_pos_dens "lem_rn_unimodal_pack"]
theorem finsum_mem_le_iSup_add_inv_mul_finsum (a : ℤ → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hfin : (Function.support a).Finite)
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
  have hM0 : 0 ≤ ⨆ x, a x := le_trans (ha 0) (hM 0)
  set T := s.filter (· ∈ Z) with hT
  have hZ : ∑ᶠ z ∈ Z, a z = ∑ z ∈ T, a z := by
    rw [← finsum_mem_inter_support, ← finsum_mem_coe_finset]
    congr 1
    ext x
    simp [hT, hs, and_comm]
  have hS : ∑ᶠ x, a x = ∑ x ∈ s, a x :=
    finsum_eq_sum_of_support_subset a (fun x hx => hsupp x hx)
  rw [hZ, hS]
  exact sum_le_add_inv_mul_sum_of_unimodal hρ T
    (fun z hz z' hz' h => hsep z (Finset.mem_filter.mp hz).2 z' (Finset.mem_filter.mp hz').2 h)
    s a ha hsupp huni _ hM0 hM

end CollatzPosDens
