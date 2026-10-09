/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnCrossE
public import CollatzPosDens.Renewal.RnCrossP
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnCrossLaw
public import CollatzPosDens.Renewal.RnCrossMax
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.Renewal.RnRawOddSum
public import CollatzPosDens.Renewal.RnUnimodalPack
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Packing of the horizontal crossing coordinate

Let `G ≥ 1024` be an integer, `ρ > 0`, and let `Z ⊆ ℤ` be `ρ`-separated: `ρ ≤ |z - z'|` for all
distinct `z, z' ∈ Z` (`Z` may be infinite). Then the column masses of the first-passage law
`F_G` over `Z` satisfy
$$\sum_{r\in Z}\ \sum_{\ell\in\mathbb Z}\mathsf F_G(r,\ell)
  <\frac{17}{10\sqrt G}+\frac{33}{32\,\rho}.$$

Put `t = G - 4`. Columns `r ≤ 0` carry no mass. For `r ≥ 1` the exact crossing law and
`e_t ≥ 0` bound the column mass by `e_t(r - 1) + ∑_k ν₄₅(k) p_t(r - 1 - k)`. The binomial rows
are unimodal, so `x ↦ p_t(x - 1 - k)` and `x ↦ e_t(x - 1)` have superlevel sets of consecutive
integers; their total masses are at most `1` and `1/32`. The packing lemma for unimodal
sequences bounds `∑_{r ∈ Z} p_t(r - 1 - k)` by `max p_t + 1/ρ` and `∑_{r ∈ Z} e_t(r - 1)` by
`max e_t + 1/(32ρ)`; since `∑_k ν₄₅(k) = 1`, the total is at most
`max p_t + max e_t + 33/(32ρ)`, and `max p_t + max e_t < 17/(10√G)`.

## Main results

* `CollatzPosDens.tsum_firstPassageLaw_packing_lt`: the column masses over `Z` are
  summable, and their real sum is `< 17/(10√G) + 33/(32ρ)`.
* `CollatzPosDens.tsum_firstPassageLaw_packing_lt_ennreal`: the statement as a sum in
  `[0, ∞]`.

## Implementation notes

The sum in `[0, ∞]` is the `ENNReal`-valued unconditional sum of `ENNReal.ofReal` of the
(nonnegative) terms; its finiteness is equivalent to the real-valued summability proved
alongside. The proof bounds the sum over every finite subset of `Z`
uniformly, which gives summability and the bound at once; the masses of the shifted weights
need only the upper bounds `≤ 1` and `≤ 1/32`, obtained from Pascal's rule.

## References

* [Mazur, *Collatz positive density*], §6.5.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-! ### Unimodality of binomial rows -/

private lemma packing_choose_mono {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private lemma packing_choose_unimodal (n : ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    n.choose a ≤ n.choose b ∨ n.choose c ≤ n.choose b := by
  by_cases hb : b ≤ n / 2
  · exact Or.inl (packing_choose_mono hab hb)
  · right
    by_cases hc : n < c
    · rw [Nat.choose_eq_zero_of_lt hc]; exact Nat.zero_le _
    · rw [← Nat.choose_symm (n := n) (k := c) (by omega),
        ← Nat.choose_symm (n := n) (k := b) (by omega)]
      exact packing_choose_mono (by omega) (by omega)

private lemma packing_le_choose_div {n a b c : ℕ} {D l : ℝ} (hD : 0 < D) (hab : a ≤ b)
    (hbc : b ≤ c) (ha : l ≤ (n.choose a : ℝ) / D) (hc : l ≤ (n.choose c : ℝ) / D) :
    l ≤ (n.choose b : ℝ) / D := by
  rcases packing_choose_unimodal n hab hbc with h | h
  · exact ha.trans (div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le)
  · exact hc.trans (div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le)

private lemma packing_straddleWeight_ordConnected (t : ℕ) {l : ℝ} (hl : 0 < l) :
    {j : ℤ | l ≤ straddleWeight t j}.OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hx0 : 0 ≤ x := by
    by_contra h
    rw [straddleWeight_of_neg t (not_le.1 h)] at hx; linarith
  have hz0 : 0 ≤ z := hx0.trans hz.1
  have hy0 : 0 ≤ y := hz0.trans hz.2
  rw [straddleWeight_of_nonneg t hx0] at hx
  rw [straddleWeight_of_nonneg t hy0] at hy
  rw [straddleWeight_of_nonneg t hz0]
  exact packing_le_choose_div (by positivity) (by have := hz.1; omega)
    (by have := hz.2; omega) hx hy

private lemma packing_boundaryWeight_ordConnected (t : ℕ) {l : ℝ} (hl : 0 < l) :
    {j : ℤ | l ≤ boundaryWeight t j}.OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hpos : ∀ {j : ℤ}, l ≤ boundaryWeight t j → 1 ≤ t ∧ 1 ≤ j := fun {j} h => by
    by_contra hc
    rw [boundaryWeight_of_not hc] at h; linarith
  obtain ⟨ht, hx1⟩ := hpos hx
  have hz1 : 1 ≤ z := hx1.trans hz.1
  have hy1 : 1 ≤ y := hz1.trans hz.2
  rw [boundaryWeight_of_pos ht hx1, div_div] at hx
  rw [boundaryWeight_of_pos ht hy1, div_div] at hy
  rw [boundaryWeight_of_pos ht hz1, div_div]
  exact packing_le_choose_div (by positivity) (by have := hz.1; omega)
    (by have := hz.2; omega) hx hy

/-! ### Supports and masses of the crossing weights -/

private lemma packing_straddleWeight_support (t : ℕ) {j : ℤ} (h : straddleWeight t j ≠ 0) :
    0 ≤ j ∧ j ≤ t := by
  by_contra hc
  apply h
  rcases not_and_or.1 hc with h0 | ht
  · exact straddleWeight_of_neg t (not_le.1 h0)
  · rw [straddleWeight_of_nonneg t (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma packing_boundaryWeight_support (t : ℕ) {j : ℤ} (h : boundaryWeight t j ≠ 0) :
    1 ≤ j ∧ j ≤ t := by
  by_contra hc
  apply h
  by_cases h1 : 1 ≤ t ∧ 1 ≤ j
  · rw [boundaryWeight_of_pos h1.1 h1.2, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · exact boundaryWeight_of_not h1

private lemma packing_sum_range_choose_le (m K : ℕ) : ∑ i ∈ range K, m.choose i ≤ 2 ^ m := by
  rw [← Finset.sum_filter_of_ne (p := fun i => i ≤ m) (fun i _ hi => by
    by_contra h; exact hi (Nat.choose_eq_zero_of_lt (by omega))), ← Nat.sum_range_choose m]
  exact Finset.sum_le_sum_of_subset (fun i hi => by simp at hi ⊢; omega)

private lemma packing_sum_straddleWeight_le (t N : ℕ) :
    ∑ j ∈ range N, straddleWeight t j ≤ 1 := by
  simp only [straddleWeight_natCast]
  rw [← Finset.sum_div, div_le_one (by positivity)]
  have := (sum_range_choose_succ_odd t N).trans_le (packing_sum_range_choose_le t (2 * N))
  exact_mod_cast this

private lemma packing_sum_boundaryWeight_le (n N : ℕ) :
    ∑ j ∈ range N, boundaryWeight (n + 1 + 1) ((j : ℤ) + 1) ≤ 1 / 32 := by
  simp only [boundaryWeight_succ_natCast_succ]
  rw [← Finset.sum_div, ← Finset.sum_div, div_div, div_le_iff₀ (by positivity)]
  have h := (sum_range_choose_succ_odd n N).trans_le
    (packing_sum_range_choose_le n (2 * N))
  have h' : (∑ j ∈ range N, ((n + 1).choose (2 * j + 1) : ℝ)) ≤ 2 ^ n := by exact_mod_cast h
  calc _ ≤ (2 : ℝ) ^ n := h'
    _ = 1 / 32 * (8 * 2 ^ (n + 1 + 1)) := by ring

private lemma packing_exists_max (f : ℤ → ℝ) (hf : ∀ x, 0 ≤ f x) (s : Finset ℤ)
    (hs : s.Nonempty) (hsupp : ∀ x, f x ≠ 0 → x ∈ s) : ∃ x0, ∀ x, f x ≤ f x0 := by
  obtain ⟨x0, -, h⟩ := s.exists_max_image f hs
  refine ⟨x0, fun x => ?_⟩
  by_cases hx : f x = 0
  · rw [hx]; exact hf x0
  · exact h x (hsupp x hx)

private lemma packing_summable_col (G : ℕ) (hG : 5 ≤ G) (r : ℤ) :
    Summable (fun ℓ : ℤ => firstPassageLaw G (r, ℓ)) := by
  rcases le_or_gt r 0 with hr | hr
  · have : (fun ℓ : ℤ => firstPassageLaw G (r, ℓ)) = 0 := by
      funext ℓ
      by_contra h
      have := (firstPassageLaw_support h).1
      simp only at this
      omega
    rw [this]; exact summable_zero
  · obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
    exact (hasSum_firstPassageLaw_cross hG (by omega)).summable

/-! ### The packing bound -/

/-- **Packing of the horizontal crossing coordinate**, real form. For an integer `G ≥ 1024`,
`ρ > 0` and a `ρ`-separated `Z ⊆ ℤ`, the column masses `∑_ℓ F_G(r, ℓ)`, `r ∈ Z`, are summable
with sum `< 17/(10√G) + 33/(32ρ)`. -/
theorem tsum_firstPassageLaw_packing_lt {G : ℕ} (hG : 1024 ≤ G) {ρ : ℝ} (hρ : 0 < ρ)
    (Z : Set ℤ) (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → ρ ≤ |(z : ℝ) - z'|) :
    Summable (fun r : Z => ∑' ℓ : ℤ, firstPassageLaw G ((r : ℤ), ℓ)) ∧
      ∑' r : Z, ∑' ℓ : ℤ, firstPassageLaw G ((r : ℤ), ℓ) <
        17 / (10 * Real.sqrt G) + 33 / (32 * ρ) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, G - 4 = n + 1 + 1 := ⟨G - 6, by omega⟩
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℝ, F = fun r => ∑' ℓ : ℤ, firstPassageLaw G (r, ℓ) := ⟨_, rfl⟩
  obtain ⟨j0, hj0⟩ := packing_exists_max (straddleWeight (G - 4)) (straddleWeight_nonneg _)
    (Icc 0 (G - 4 : ℕ)) ⟨0, by simp⟩
    (fun x hx => mem_Icc.2 (packing_straddleWeight_support _ hx))
  obtain ⟨j1, hj1⟩ := packing_exists_max (boundaryWeight (G - 4)) (boundaryWeight_nonneg _)
    (Icc 1 (G - 4 : ℕ)) ⟨1, by simp only [mem_Icc]; omega⟩
    (fun x hx => mem_Icc.2 (packing_boundaryWeight_support _ hx))
  have hmax := straddleWeight_add_boundaryWeight_lt hG j0 j1
  have hgs : ∀ r : ℤ, Summable (fun k => nu45 k * straddleWeight (G - 4) (r - 1 - k)) :=
    fun r => Summable.of_nonneg_of_le
      (fun k => mul_nonneg (nu45_nonneg k) (straddleWeight_nonneg _ _))
      (fun k => mul_le_mul_of_nonneg_left (hj0 _) (nu45_nonneg k))
      (summable_nu45.mul_right _)
  have hcol : ∀ r : ℤ, F r ≤ boundaryWeight (G - 4) (r - 1) +
      ∑' k, nu45 k * straddleWeight (G - 4) (r - 1 - k) := by
    intro r
    have hg0 : 0 ≤ ∑' k, nu45 k * straddleWeight (G - 4) (r - 1 - k) :=
      tsum_nonneg fun k => mul_nonneg (nu45_nonneg k) (straddleWeight_nonneg _ _)
    rcases le_or_gt r 0 with hr | hr
    · have h0 : F r = 0 := by
        rw [hF]
        dsimp only
        rw [tsum_congr (g := fun _ => (0 : ℝ)) (fun ℓ => by
          by_contra h
          have := (firstPassageLaw_support h).1
          simp only at this
          omega), tsum_zero]
      rw [h0]
      exact add_nonneg (boundaryWeight_nonneg _ _) hg0
    · obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = r' := ⟨r.toNat, by omega⟩
      have hc := (hasSum_firstPassageLaw_cross (G := G) (r := r') (by omega) (by omega)).tsum_eq
      rw [hF]
      dsimp only
      rw [hc]
      gcongr
      calc ∑ j ∈ range (r' - 1), (straddleWeight (G - 4) j - boundaryWeight (G - 4) j) *
              nu45 ((r' : ℤ) - 1 - j)
          ≤ ∑ j ∈ range (r' - 1), straddleWeight (G - 4) j * nu45 ((r' : ℤ) - 1 - j) :=
            sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
              (sub_le_self _ (boundaryWeight_nonneg _ _)) (nu45_nonneg _)
        _ = ∑ k ∈ (range (r' - 1)).image (fun j : ℕ => (r' : ℤ) - 1 - j),
              nu45 k * straddleWeight (G - 4) ((r' : ℤ) - 1 - k) := by
            rw [sum_image (fun a _ b _ h => by omega)]
            refine sum_congr rfl fun j _ => ?_
            rw [show (r' : ℤ) - 1 - ((r' : ℤ) - 1 - j) = j by ring, mul_comm]
        _ ≤ _ := (hgs r').sum_le_tsum _ fun k _ =>
            mul_nonneg (nu45_nonneg k) (straddleWeight_nonneg _ _)
  have hfin : ∀ T : Finset ℤ, (∀ r ∈ T, r ∈ Z) → ∑ r ∈ T, F r ≤
      straddleWeight (G - 4) j0 + boundaryWeight (G - 4) j1 + 33 / 32 * ρ⁻¹ := by
    intro T hT
    have hsepT : ∀ z ∈ T, ∀ z' ∈ T, z ≠ z' → ρ ≤ |(z : ℝ) - z'| :=
      fun z hz z' hz' h => hsep z (hT z hz) z' (hT z' hz') h
    have he_pack : ∑ r ∈ T, boundaryWeight (G - 4) (r - 1) ≤
        boundaryWeight (G - 4) j1 + ρ⁻¹ * (1 / 32) := by
      have := sum_le_add_inv_mul_sum_of_unimodal hρ T hsepT
        ((range (G - 4)).image fun j : ℕ => (j : ℤ) + 2)
        (fun x => boundaryWeight (G - 4) (x - 1)) (fun x => boundaryWeight_nonneg _ _)
        (fun x hx => by
          have := packing_boundaryWeight_support (G - 4) hx
          simp only [mem_image, mem_range]
          exact ⟨(x - 2).toNat, by omega, by omega⟩)
        (fun l hl => Set.ordConnected_preimage (OrderIso.subRight 1)
          (hs := packing_boundaryWeight_ordConnected _ hl))
        _ (boundaryWeight_nonneg _ _) (fun x => hj1 _)
      refine this.trans (add_le_add_right (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ.le)) _)
      rw [sum_image (fun a _ b _ h => by omega)]
      have h21 : ∀ j : ℕ, (j : ℤ) + 2 - 1 = (j : ℤ) + 1 := fun j => by ring
      simp only [h21]
      rw [hn]
      exact packing_sum_boundaryWeight_le n _
    have hp_pack : ∀ k : ℤ, ∑ r ∈ T, straddleWeight (G - 4) (r - 1 - k) ≤
        straddleWeight (G - 4) j0 + ρ⁻¹ := by
      intro k
      have := sum_le_add_inv_mul_sum_of_unimodal hρ T hsepT
        ((range (G - 4 + 1)).image fun j : ℕ => (j : ℤ) + (1 + k))
        (fun x => straddleWeight (G - 4) (x - (1 + k))) (fun x => straddleWeight_nonneg _ _)
        (fun x hx => by
          have := packing_straddleWeight_support (G - 4) hx
          simp only [mem_image, mem_range]
          exact ⟨(x - (1 + k)).toNat, by omega, by omega⟩)
        (fun l hl => Set.ordConnected_preimage (OrderIso.subRight (1 + k))
          (hs := packing_straddleWeight_ordConnected _ hl))
        _ (straddleWeight_nonneg _ _) (fun x => hj0 _)
      simp only [sub_sub]
      refine this.trans (add_le_add_right ?_ _)
      calc ρ⁻¹ * _ ≤ ρ⁻¹ * 1 := mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ.le)
        _ = ρ⁻¹ := mul_one _
      rw [sum_image (fun a _ b _ h => by omega)]
      simp only [add_sub_cancel_right]
      exact packing_sum_straddleWeight_le _ _
    have hg_pack : ∑ r ∈ T, ∑' k, nu45 k * straddleWeight (G - 4) (r - 1 - k) ≤
        straddleWeight (G - 4) j0 + ρ⁻¹ := by
      rw [← Summable.tsum_finsetSum (fun r _ => hgs r)]
      simp_rw [← Finset.mul_sum]
      have hle : ∀ k, nu45 k * ∑ r ∈ T, straddleWeight (G - 4) (r - 1 - k) ≤
          nu45 k * (straddleWeight (G - 4) j0 + ρ⁻¹) :=
        fun k => mul_le_mul_of_nonneg_left (hp_pack k) (nu45_nonneg k)
      calc ∑' k, nu45 k * ∑ r ∈ T, straddleWeight (G - 4) (r - 1 - k)
          ≤ ∑' k, nu45 k * (straddleWeight (G - 4) j0 + ρ⁻¹) :=
            Summable.tsum_le_tsum hle
              (Summable.of_nonneg_of_le (fun k => mul_nonneg (nu45_nonneg k)
                (sum_nonneg fun r _ => straddleWeight_nonneg _ _)) hle
                (summable_nu45.mul_right _))
              (summable_nu45.mul_right _)
        _ = _ := by rw [tsum_mul_right, tsum_nu45, one_mul]
    calc ∑ r ∈ T, F r ≤ ∑ r ∈ T, (boundaryWeight (G - 4) (r - 1) +
          ∑' k, nu45 k * straddleWeight (G - 4) (r - 1 - k)) := sum_le_sum fun r _ => hcol r
      _ = _ := sum_add_distrib
      _ ≤ _ := by linarith
  have hFnn : ∀ r, 0 ≤ F r := fun r => by
    rw [hF]; exact tsum_nonneg fun ℓ => firstPassageLaw_nonneg _ _
  have hbound : ∀ u : Finset Z, ∑ r ∈ u, F r ≤
      straddleWeight (G - 4) j0 + boundaryWeight (G - 4) j1 + 33 / 32 * ρ⁻¹ := fun u => by
    have := hfin (u.map (Function.Embedding.subtype _)) (fun r hr => by
      obtain ⟨x, -, rfl⟩ := mem_map.1 hr; exact x.2)
    rwa [sum_map] at this
  have hS : Summable (fun r : Z => F r) := summable_of_sum_le (fun r => hFnn r) hbound
  have h33 : 33 / 32 * ρ⁻¹ = 33 / (32 * ρ) := by field_simp
  subst hF
  exact ⟨hS, (hS.tsum_le_of_sum_le hbound).trans_lt (by linarith)⟩

/-- **Packing of the horizontal crossing coordinate**. Let `G ≥ 1024` be an integer, `ρ > 0`,
and `Z ⊆ ℤ` with `ρ ≤ |z - z'|` for all distinct `z, z' ∈ Z` (`Z` may be infinite). Then, as a
sum in `[0, ∞]`, `∑_{r ∈ Z} ∑_{ℓ ∈ ℤ} F_G(r, ℓ) < 17/(10√G) + 33/(32ρ)`. -/
@[collatz_pos_dens "lem_rn_fp_packing"]
theorem tsum_firstPassageLaw_packing_lt_ennreal {G : ℕ} (hG : 1024 ≤ G) {ρ : ℝ} (hρ : 0 < ρ)
    (Z : Set ℤ) (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → ρ ≤ |(z : ℝ) - z'|) :
    ∑' r : Z, ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw G ((r : ℤ), ℓ)) <
      ENNReal.ofReal (17 / (10 * Real.sqrt G) + 33 / (32 * ρ)) := by
  obtain ⟨hS, hlt⟩ := tsum_firstPassageLaw_packing_lt hG hρ Z hsep
  have hin : ∀ r : Z, ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw G ((r : ℤ), ℓ)) =
      ENNReal.ofReal (∑' ℓ : ℤ, firstPassageLaw G ((r : ℤ), ℓ)) := fun r =>
    (ENNReal.ofReal_tsum_of_nonneg (fun ℓ => firstPassageLaw_nonneg _ _)
      (packing_summable_col G (by omega) r)).symm
  rw [tsum_congr hin, ← ENNReal.ofReal_tsum_of_nonneg
    (fun r => tsum_nonneg fun ℓ => firstPassageLaw_nonneg _ _) hS]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt

end CollatzPosDens
