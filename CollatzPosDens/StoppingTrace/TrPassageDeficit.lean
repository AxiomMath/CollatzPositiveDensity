/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Transfer.S02Gamma
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrCountMono
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrPassageLaw
public import CollatzPosDens.StoppingTrace.TrPassageRaw3
public import CollatzPosDens.StoppingTrace.TrRaw3LastBlock
public import CollatzPosDens.StoppingTrace.TrRaw3Witness
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# Deficit of a passage from first raw crossings

Let `s ∈ ℕ`, let `I` be a finite set of triples `(c, o, r)` with `1 ≤ o ≤ c` and `r ≥ 1`, and
suppose that on each first raw crossing event `𝒳_{c,o,r}(s)`, `(c, o, r) ∈ I`, the tilt
`e^{-γ_* N^*(v, π; |π|)}` is at most `b_{c,o,r}`. Then
```
∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}
  ≤ 1 - ∑_{(c,o,r) ∈ I} (1 - b_{c,o,r}) ϖ(c) 𝖱(r - 1, s + o - c).
```
The events `𝒳_{c,o,r}(s)` are pairwise disjoint: the raw partial sums of a live list are
nondecreasing, and `σ_{r-1}(π) = s + o - c ≤ s < s + o = σ_r(π)` singles out `r` as the first
raw crossing of level `s`, whence also `c` (the `r`-th letter) and `o`. Pointwise the tilt is at
most `1` (as `N^* ≥ 0` and `γ_* > 0`) and at most `b_{c,o,r}` on `𝒳_{c,o,r}(s)`; summing against
`bw^⊗` over `Π_s`, whose total mass is `1`, and using the mass `ϖ(c) 𝖱(r - 1, s + o - c)` of
`𝒳_{c,o,r}(s)` gives the claim.

## Main results

* `CollatzPosDens.trRawThreeWitness_eq_of_mem`: two first raw crossing events containing a
  common list have the same triple.
* `CollatzPosDens.tsum_trPassage_mul_exp_neg_trCount_le_one_sub`: the deficit bound.

## Implementation notes

A triple is an element of `ℤ × ℤ × ℕ`, the position `r` being a natural number as in
`trRawThreeWitness`. No hypothesis `v ∈ 𝒫`, `c ≥ 2` or `b_{c,o,r} ∈ [0, 1]` is needed: the base
point `v` is any point of `ℤ × ℤ`, and the bound holds for any real numbers `b_{c,o,r}`. The
level `n` and the residue `ξ` defining `N^*` are arbitrary.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The raw partial sums of a list of blocks of nonzero weight are nondecreasing. -/
theorem trRawSum_mono {π : List (List ℤ × ℤ)} (h : ∀ b ∈ π, chBlockWeight b ≠ 0) {i j : ℕ}
    (hij : i ≤ j) : trRawSum π i ≤ trRawSum π j := by
  rw [trRawSum_eq_sum_take, trRawSum_eq_sum_take]
  set z := π.flatMap fun b => b.1 ++ [b.2]
  have hnn : ∀ x ∈ z, 0 ≤ x := fun x hx ↦ by
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hx
    have := two_le_of_mem_append_of_chBlockWeight_ne_zero (h b hb) hxb
    omega
  have hsplit : z.take j = z.take i ++ (z.take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i (z.take j)]
    rw [List.take_take, min_eq_left hij]
  rw [hsplit, List.sum_append]
  have : 0 ≤ ((z.take j).drop i).sum :=
    List.sum_nonneg fun x hx ↦ hnn x (List.mem_of_mem_take (List.mem_of_mem_drop hx))
  omega

/-- For `π ∈ 𝒳_{c,o,r}(s)` with `r ≥ 1`, `σ_{r-1}(π) = s + o - c`. -/
theorem trRawSum_pred_of_mem_trRawThreeWitness {s : ℕ} {c o : ℤ} {r : ℕ}
    {π : List (List ℤ × ℤ)} (hπ : π ∈ trRawThreeWitness s c o r) (hr : 1 ≤ r) :
    trRawSum π (r - 1) = s + o - c := by
  obtain ⟨hlt, hc⟩ := trRawThreeWitness_getElem_flatMap hπ
  have h := trRawSum_succ π hlt
  rw [Nat.sub_add_cancel hr, trRawThreeWitness_trRawSum hπ, hc] at h
  omega

/-- **Disjointness of the first raw crossing events.** If a list lies in `𝒳_{c,o,r}(s)` and in
`𝒳_{c',o',r'}(s)`, where `1 ≤ o ≤ c`, `1 ≤ o' ≤ c'` and `r, r' ≥ 1`, then
`(c, o, r) = (c', o', r')`. -/
theorem trRawThreeWitness_eq_of_mem {s : ℕ} {c o c' o' : ℤ} {r r' : ℕ}
    {π : List (List ℤ × ℤ)} (h : π ∈ trRawThreeWitness s c o r)
    (h' : π ∈ trRawThreeWitness s c' o' r') (ho : 1 ≤ o) (hoc : o ≤ c) (hr : 1 ≤ r)
    (ho' : 1 ≤ o') (hoc' : o' ≤ c') (hr' : 1 ≤ r') : c = c' ∧ o = o' ∧ r = r' := by
  have hlive := trLive_of_mem_trPassage (trRawThreeWitness_mem_trPassage h)
  have hw : ∀ b ∈ π, chBlockWeight b ≠ 0 := fun b hb ↦ hlive b hb
  have hσ := trRawThreeWitness_trRawSum h
  have hσ' := trRawThreeWitness_trRawSum h'
  have hp := trRawSum_pred_of_mem_trRawThreeWitness h hr
  have hp' := trRawSum_pred_of_mem_trRawThreeWitness h' hr'
  have hrr : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · have := trRawSum_mono hw (show r ≤ r' - 1 by omega)
      omega
    · exact heq
    · have := trRawSum_mono hw (show r' ≤ r - 1 by omega)
      omega
  subst hrr
  obtain ⟨hlt, hc⟩ := trRawThreeWitness_getElem_flatMap h
  obtain ⟨hlt', hc'⟩ := trRawThreeWitness_getElem_flatMap h'
  refine ⟨hc.symm.trans hc', by omega, rfl⟩

/-- The passage lists carry total weight `1`: `∑_{π ∈ Π_s} bw^⊗(π) = 1`. -/
theorem hasSum_trListWeight_trPassage (s : ℕ) :
    HasSum (fun π : trPassage s ↦ trListWeight π.1) 1 := by
  have h := tsum_trPassage_eq_tsum_firstPassageLaw s (fun _ ↦ 1)
  simp only [mul_one] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ firstPassageLaw_nonneg _ x)
    (summable_firstPassageLaw s), tsum_firstPassageLaw, ENNReal.ofReal_one] at h
  have hne : ∑' π : trPassage s, ENNReal.ofReal (trListWeight π.1) ≠ ⊤ := by simp [h]
  have hs := ENNReal.summable_toReal hne
  simp only [ENNReal.toReal_ofReal (trListWeight_nonneg _)] at hs
  convert hs.hasSum
  rw [← ENNReal.toReal_one, ← h, ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
  simp [ENNReal.toReal_ofReal (trListWeight_nonneg _)]

/-- The weight of `𝒳_{c,o,r}(s)`, as a series over the passage lists. -/
theorem hasSum_indicator_trRawThreeWitness (s : ℕ) {c o : ℤ} {r : ℕ} (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) :
    HasSum (fun π : trPassage s ↦ (trRawThreeWitness s c o r).indicator trListWeight π.1)
      (varpi c * rawMass (r - 1) (s + o - c)) := by
  have h := (hasSum_subtype_iff_indicator (f := trListWeight)).mp
    (hasSum_trListWeight_trRawThreeWitness s ho hoc hr)
  refine (hasSum_subtype_iff_indicator
    (f := (trRawThreeWitness s c o r).indicator trListWeight)).mpr ?_
  rwa [Set.indicator_indicator,
    Set.inter_eq_right.mpr (trRawThreeWitness_subset_trPassage s c o r)]

/-- **Deficit of a passage from first raw crossings.** Let `s ∈ ℕ`, let `I` be a finite set of
triples `(c, o, r)` with `1 ≤ o ≤ c` and `r ≥ 1`, and let `b_{c,o,r}` be real numbers with
`e^{-γ_* N^*(v, π; |π|)} ≤ b_{c,o,r}` for every `π ∈ 𝒳_{c,o,r}(s)`. Then
`∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)} ≤
1 - ∑_{(c,o,r) ∈ I} (1 - b_{c,o,r}) ϖ(c) 𝖱(r - 1, s + o - c)`. -/
@[collatz_pos_dens "lem_tr_passage_deficit"]
theorem tsum_trPassage_mul_exp_neg_trCount_le_one_sub {n : ℕ} (ξ : ResidueGroup n)
    (v : ℤ × ℤ) (s : ℕ) (I : Finset (ℤ × ℤ × ℕ)) (b : ℤ × ℤ × ℕ → ℝ)
    (hI : ∀ t ∈ I, 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2)
    (hb : ∀ t ∈ I, ∀ π ∈ trRawThreeWitness s t.1 t.2.1 t.2.2,
      Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length) ≤ b t) :
    ∑' π : trPassage s,
        trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) ≤
      1 - ∑ t ∈ I, (1 - b t) * (varpi t.1 * rawMass (t.2.2 - 1) (s + t.2.1 - t.1)) := by
  have hγ : (0 : ℝ) < gammaStar := by exact_mod_cast gammaStar_pos
  set X : ℤ × ℤ × ℕ → Set (List (List ℤ × ℤ)) := fun t ↦ trRawThreeWitness s t.1 t.2.1 t.2.2
  have hg : HasSum (fun π : trPassage s ↦ trListWeight π.1 -
      ∑ t ∈ I, (1 - b t) * (X t).indicator trListWeight π.1)
      (1 - ∑ t ∈ I, (1 - b t) * (varpi t.1 * rawMass (t.2.2 - 1) (s + t.2.1 - t.1))) :=
    (hasSum_trListWeight_trPassage s).sub (hasSum_sum fun t ht ↦
      (hasSum_indicator_trRawThreeWitness s (hI t ht).1 (hI t ht).2.1 (hI t ht).2.2).mul_left _)
  have hle1 : ∀ π : List (List ℤ × ℤ),
      Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length) ≤ 1 := fun π ↦
    Real.exp_le_one_iff.mpr (by nlinarith [trCount_nonneg (n := n) (ξ := ξ) v π π.length])
  have hpt : ∀ π : trPassage s,
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) ≤
        trListWeight π.1 - ∑ t ∈ I, (1 - b t) * (X t).indicator trListWeight π.1 := by
    intro π
    have hw := trListWeight_nonneg π.1
    by_cases hex : ∃ t ∈ I, π.1 ∈ X t
    · obtain ⟨t₀, ht₀, hπ₀⟩ := hex
      rw [Finset.sum_eq_single_of_mem t₀ ht₀ fun t ht hne ↦ by
        rw [Set.indicator_of_notMem, mul_zero]
        intro hπ
        obtain ⟨h1, h2, h3⟩ := trRawThreeWitness_eq_of_mem hπ hπ₀ (hI t ht).1 (hI t ht).2.1
          (hI t ht).2.2 (hI t₀ ht₀).1 (hI t₀ ht₀).2.1 (hI t₀ ht₀).2.2
        exact hne (Prod.ext h1 (Prod.ext h2 h3))]
      rw [Set.indicator_of_mem hπ₀]
      have := mul_le_mul_of_nonneg_left (hb t₀ ht₀ π.1 hπ₀) hw
      linarith
    · push Not at hex
      rw [Finset.sum_eq_zero fun t ht ↦ by rw [Set.indicator_of_notMem (hex t ht), mul_zero]]
      have := mul_le_mul_of_nonneg_left (hle1 π.1) hw
      linarith
  have hf : Summable fun π : trPassage s ↦
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) :=
    (hasSum_trListWeight_trPassage s).summable.of_nonneg_of_le
      (fun π ↦ mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le)
      fun π ↦ mul_le_of_le_one_right (trListWeight_nonneg _) (hle1 π.1)
  exact hasSum_le hpt hf.hasSum hg

end CollatzPosDens
