/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrPacketRange
public import CollatzPosDens.StoppingTrace.TrTailGain
public import CollatzPosDens.StoppingTrace.TrTreeCostLeaves
public import CollatzPosDens.StoppingTrace.TrTreeCylinderMass
public import CollatzPosDens.StoppingTrace.TrTreeLeafPrefix
public import CollatzPosDens.StoppingTrace.TrTreeLeafReward
public import CollatzPosDens.StoppingTrace.TrTreeTailReward

/-!
# The paid cylinder bound of an entry tree

Fix a level `n`, a unit `ξ ∈ G_n` and the colour scale `ε_*`. Let `v ∈ 𝒫` be black with gap
`ω = gap(v)`, let `H ∈ ℕ`, `m ∈ ℤ` and `α ∈ ℝ` be such that
`ϑ(v + (r, L)) - 9^{r-1} (2^ω m + α) / 2^L ∈ ℤ` for all integers `r ≥ 1` and `0 ≤ L ≤ H`, and let
`(cut, W)` be a tree datum of height `H` whose policy `W` is valid at `v`. Then
```
m_1(v) ≤ F^{cut,W}_{0,0}(2^ω m + α) - T^{root}_{ω,cut(0)}.
```

Put `X = 2^ω m + α`. Since `m_0 = 1`, `m_1(v) = ∑_{u ∈ 𝓔(v)} bw^⊗(u) e^{-γ_* N^*(v, u; |u|)}`.
Every entry list `u ∈ 𝓔(v)` has a raw word beginning with exactly one leaf `λ ∈ 𝔏^W(0, 0)`,
and along that leaf
`e^{-γ_* N^*(v, u; |u|)} ≤ w_λ = ∏_{i=1}^{|λ|} ψ^cut_{i-1, λ_1 + ⋯ + λ_{i-1}, λ_i}(X)`.
For the one-letter leaves `(c)` with `max {cut(0), ω, 2} < c ≤ 16` one has `w_{(c)} = 1`, and the
first letter alone gives the better bound `1 - δ^{pk}_{c,c-ω}`. The entry lists beginning with
`λ` have total weight at most `∏_i ϖ(λ_i)`, so
```
m_1(v) ≤ ∑_{λ ∈ 𝔏^W(0,0)} (∏_i ϖ(λ_i)) w_λ - ∑_{c} ϖ(c) δ^{pk}_{c,c-ω},
```
and the two sums are `F^{cut,W}_{0,0}(X)` and `T^{root}_{ω,cut(0)}`.

## Main results

* `CollatzPosDens.tsum_trEntryWords_ite_prefix_le_prod_varpi`: the entry lists whose raw word
  begins with a word `λ` have total weight at most `∏_i ϖ(λ_i)`.
* `CollatzPosDens.trKernel_one_le_ofReal_trTreeCost_sub_trTailGain`: the paid cylinder bound
  `m_1(v) ≤ F^{cut,W}_{0,0}(2^ω m + α) - T^{root}_{ω,cut(0)}`.

## Implementation notes

The number `m_1(v)` lies in `[0, ∞]`, and the bound is stated as
`m_1(v) ≤ ENNReal.ofReal (F^{cut,W}_{0,0}(X) - T^{root}_{ω,cut(0)})`; the proof shows that the
real number on the right is a sum of nonnegative terms, so nothing is truncated. The gap of a
black point is a nonnegative integer; it is given as a natural number `ω` together with the
equation `gap(v) = ω`. Black points are points of `𝒫` and the residue `ξ` is a unit: these are
the hypotheses `v ∈ bkPoints` and `IsResidueUnit ξ`. The integer `r ≥ 1` is taken in `ℕ`, and
membership in `ℤ` is the existence of an integer equal to the difference.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The entry lists `u ∈ 𝓔(v)` whose raw word `raw_{M_u}(u)` begins with a word `λ` have total
weight at most `∏_i ϖ(λ_i)`. -/
theorem tsum_trEntryWords_ite_prefix_le_prod_varpi (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    (v : ℤ × ℤ) (l : List ℤ) :
    ∑' u : trEntryWords n ξ ε v,
      (if l <+: chRaw (chBlockPath u.1 u.1.length).1.toNat u.1 then
        ENNReal.ofReal (trListWeight u.1) else 0) ≤
      ENNReal.ofReal (∏ i : Fin l.length, varpi l[i]) := by
  classical
  have h := tsum_trListWeight_trEntryWords_chRaw_le n ξ ε v l.length fun i ↦ l[i]
  have hl : (List.ofFn fun i : Fin l.length ↦ l[i]) = l :=
    List.ext_getElem (by simp) fun i _ _ ↦ by simp
  rw [hl] at h
  refine le_trans (le_of_eq ?_) h
  have h' : ∑' u : {u // u ∈ trEntryWords n ξ ε v ∧ chRaw l.length u = l},
      ENNReal.ofReal (trListWeight u.1) =
        ∑' u, {u | u ∈ trEntryWords n ξ ε v ∧ chRaw l.length u = l}.indicator
          (fun u ↦ ENNReal.ofReal (trListWeight u)) u :=
    tsum_subtype {u | u ∈ trEntryWords n ξ ε v ∧ chRaw l.length u = l}
      (fun u ↦ ENNReal.ofReal (trListWeight u))
  rw [tsum_subtype (trEntryWords n ξ ε v) (fun u ↦
      if l <+: chRaw (chBlockPath u u.length).1.toNat u then
        ENNReal.ofReal (trListWeight u) else 0), h']
  refine tsum_congr fun u ↦ ?_
  rw [Set.indicator_apply, Set.indicator_apply]
  simp only [chRaw_toNat_chBlockPath_fst, chRaw_eq_iff_prefix]
  by_cases hu : u ∈ trEntryWords n ξ ε v <;> simp [hu]

/-- **The paid cylinder bound of an entry tree.** Let `ξ` be a unit, `v ∈ 𝒫` black for `ε_*`
with `gap(v) = ω`, `H ∈ ℕ`, `m ∈ ℤ` and `α ∈ ℝ` such that
`ϑ(v + (r, L)) - 9^{r-1} (2^ω m + α) / 2^L ∈ ℤ` for all integers `r ≥ 1` and `0 ≤ L ≤ H`, and let
`(cut, W)` be a tree datum of height `H` with `W` valid at `v`. Then
`m_1(v) ≤ F^{cut,W}_{0,0}(2^ω m + α) - T^{root}_{ω,cut(0)}`. -/
@[collatz_pos_dens "lem_tr_tree_cylinder_bound"]
theorem trKernel_one_le_ofReal_trTreeCost_sub_trTailGain {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v)
    {ω : ℕ} (hgap : trGap n ξ (epsStar : ℝ) v = ω) {H : ℕ} {m : ℤ} {α : ℝ}
    (hθ : ∀ r : ℕ, 1 ≤ r → ∀ L : ℤ, 0 ≤ L → L ≤ H →
      ∃ k : ℤ, bkTheta n ξ (v + ((r : ℤ), L)) -
        9 ^ (r - 1) * ((2 : ℝ) ^ ω * m + α) / (2 : ℝ) ^ L = k)
    (D : TreeDatum H) (hW : TrTreeValid n ξ (epsStar : ℝ) v D.W) :
    trKernel n ξ 1 v ≤ ENNReal.ofReal
      (trTreeCost D.cut D.W 0 0 ((2 : ℝ) ^ ω * m + α) - trTailGain ω (D.cut 0)) := by
  classical
  set X : ℝ := (2 : ℝ) ^ ω * m + α with hX
  set E := trEntryWords n ξ (epsStar : ℝ) v with hE
  set L := trTreeLeaves D.W 0 0 with hL
  set R := Finset.Icc (max (D.cut 0) (max ω 2) + 1) 16 with hR
  set raw : List (List ℤ × ℤ) → List ℤ := fun u ↦ chRaw (chBlockPath u u.length).1.toNat u
    with hraw
  set P : List ℤ → ℝ := fun l ↦ ∏ i : Fin l.length, varpi l[i] with hP
  set w : List ℤ → ℝ := fun l ↦
    ∏ i : Fin l.length, trTreeFactor D.cut i (l.take i).sum.toNat l[i] X with hw
  set τ : List ℤ → ℝ := fun l ↦
    ∑ c ∈ R, if l = [(c : ℤ)] then (trPacketDeficit c (c - ω) : ℝ) else 0 with hτ
  have hP0 : ∀ l, 0 ≤ P l := fun l ↦ Finset.prod_nonneg fun i _ ↦ varpi_nonneg _
  have hw0 : ∀ l, 0 ≤ w l := fun l ↦ Finset.prod_nonneg fun i _ ↦ (trTreeFactor_pos _ _ _ _ _).le
  have hPc : ∀ c : ℤ, P [c] = varpi c := fun c ↦ by simp [hP]
  have hRmem : ∀ c ∈ R, D.cut 0 < c ∧ ω < c ∧ 2 < c ∧ c ≤ 16 := fun c hc ↦ by
    rw [hR, Finset.mem_Icc] at hc
    omega
  have hwc : ∀ c ∈ R, w [(c : ℤ)] = 1 := fun c hc ↦ by
    have := hRmem c hc
    have hw1 : w [(c : ℤ)] = trTreeFactor D.cut 0 0 (c : ℤ) X := by simp [hw]
    rw [hw1]
    exact trTreeFactor_of_not_mem (by omega) X
  have hτc : ∀ c ∈ R, τ [(c : ℤ)] = trPacketDeficit c (c - ω) := fun c hc ↦ by
    simp only [hτ]
    rw [Finset.sum_eq_single c (fun b _ hbc ↦ ite_eq_right_iff.2 fun h ↦
      (hbc (by simpa using h : c = b).symm).elim) (fun h ↦ absurd hc h)]
    simp
  have hτ0 : ∀ l, (¬∃ c ∈ R, l = [(c : ℤ)]) → τ l = 0 := fun l hl ↦
    Finset.sum_eq_zero fun c hc ↦ ite_eq_right_iff.2 fun h ↦ (hl ⟨c, hc, h⟩).elim
  have hδ : ∀ c : ℕ, (trPacketDeficit c (c - ω) : ℝ) ≤ 1 / 2 := fun c ↦ by
    have := (trPacketDeficit_mem_Icc c (c - ω)).2
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_le.2 this
  have hg0 : ∀ l, 0 ≤ w l - τ l := fun l ↦ by
    by_cases hl : ∃ c ∈ R, l = [(c : ℤ)]
    · obtain ⟨c, hc, rfl⟩ := hl
      rw [hwc c hc, hτc c hc]
      linarith [hδ c]
    · rw [hτ0 l hl, sub_zero]
      exact hw0 l
  have hrew : ∀ u ∈ E, ∀ l ∈ L, l <+: raw u →
      Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length) ≤ w l - τ l := by
    intro u hu l hl hlu
    by_cases ht : ∃ c ∈ R, l = [(c : ℤ)]
    · obtain ⟨c, hc, rfl⟩ := ht
      obtain ⟨h1, h2, h3, h4⟩ := hRmem c hc
      have hhead : (raw u).head? = some (c : ℤ) := by
        obtain ⟨t, ht⟩ := hlu
        rw [← ht]
        rfl
      rw [hwc c hc, hτc c hc]
      exact exp_neg_gammaStar_mul_trCount_le_one_sub_trPacketDeficit hξ hv hb hgap
        (by omega) h4 h2 hhead
    · rw [hτ0 l ht, sub_zero]
      exact exp_neg_gammaStar_mul_trCount_le_prod_trCapFactor hθ D hl hu hlu
  have hsumF : HasSum (fun l : L ↦ P l * w l) (trTreeCost D.cut D.W 0 0 X) := by
    convert hasSum_trTreeLeaves_trTreeCost D.isBoundedPolicy D.le_cut 0 0 X using 1
    funext l
    simp only [hP, hw, ← Finset.prod_mul_distrib, zero_add, Nat.cast_zero]
  have hRL : ∀ c ∈ R, [(c : ℤ)] ∈ L := fun c hc ↦ by
    refine singleton_mem_trTreeLeaves.2 fun hW' ↦ ?_
    obtain ⟨a, b, hab, ha, hb⟩ := hW'
    have h1 : b ≤ D.cut a := D.le_cut _ hab
    have h2 := hRmem c hc
    obtain rfl : a = 0 := by omega
    omega
  have hsumT : HasSum (fun l : L ↦ P l * τ l) (trTailGain ω (D.cut 0)) := by
    have hfun : (fun l : L ↦ P l * τ l) = fun l : L ↦ ∑ c ∈ R,
        if l.1 = [(c : ℤ)] then varpi (c : ℤ) * (trPacketDeficit c (c - ω) : ℝ) else 0 := by
      funext l
      simp only [hτ, Finset.mul_sum, mul_ite, mul_zero]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      split_ifs with h
      · rw [h, hPc]
      · rfl
    rw [hfun, trTailGain]
    refine hasSum_sum fun c hc ↦ ?_
    convert hasSum_ite_eq (⟨[(c : ℤ)], hRL c hc⟩ : L)
      (varpi (c : ℤ) * (trPacketDeficit c (c - ω) : ℝ)) using 2 with l
    simp only [Subtype.ext_iff]
  have hsum : HasSum (fun l : L ↦ P l * (w l - τ l))
      (trTreeCost D.cut D.W 0 0 X - trTailGain ω (D.cut 0)) := by
    simpa only [mul_sub] using hsumF.sub hsumT
  calc trKernel n ξ 1 v
      = ∑' u : E, ENNReal.ofReal (trListWeight u.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) := by
        rw [trKernel_succ]
        simp only [trKernel_zero, mul_one]
        rfl
    _ ≤ ∑' u : E, ∑' l : L, if l.1 <+: raw u.1 then
          ENNReal.ofReal (trListWeight u.1) * ENNReal.ofReal (w l - τ l) else 0 := by
        refine ENNReal.tsum_le_tsum fun u ↦ ?_
        obtain ⟨l₀, hl₀, huniq⟩ := existsUnique_mem_trTreeLeaves_prefix_chRaw hW u.2
        rw [tsum_eq_single ⟨l₀, hl₀.1⟩ fun l hl ↦ by
          exact ite_eq_right_iff.2 fun h ↦ (hl (Subtype.ext (huniq l.1 ⟨l.2, h⟩))).elim]
        simp only [hraw, hl₀.2, ↓reduceIte]
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hrew u.1 u.2 l₀ hl₀.1 hl₀.2)) _
    _ = ∑' l : L, ∑' u : E, if l.1 <+: raw u.1 then
          ENNReal.ofReal (trListWeight u.1) * ENNReal.ofReal (w l - τ l) else 0 :=
        ENNReal.tsum_comm
    _ ≤ ∑' l : L, ENNReal.ofReal (P l * (w l - τ l)) := by
        refine ENNReal.tsum_le_tsum fun l ↦ ?_
        calc ∑' u : E, (if l.1 <+: raw u.1 then
              ENNReal.ofReal (trListWeight u.1) * ENNReal.ofReal (w l - τ l) else 0)
            = (∑' u : E, if l.1 <+: raw u.1 then ENNReal.ofReal (trListWeight u.1) else 0) *
                ENNReal.ofReal (w l - τ l) := by
              rw [← ENNReal.tsum_mul_right]
              refine tsum_congr fun u ↦ ?_
              split_ifs <;> simp
          _ ≤ ENNReal.ofReal (P l) * ENNReal.ofReal (w l - τ l) :=
              mul_le_mul_left (tsum_trEntryWords_ite_prefix_le_prod_varpi n ξ _ v l) _
          _ = ENNReal.ofReal (P l * (w l - τ l)) := (ENNReal.ofReal_mul (hP0 l)).symm
    _ = ENNReal.ofReal (trTreeCost D.cut D.W 0 0 X - trTailGain ω (D.cut 0)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun l : L ↦ mul_nonneg (hP0 l) (hg0 l))
          hsum.summable, hsum.tsum_eq]

end CollatzPosDens
