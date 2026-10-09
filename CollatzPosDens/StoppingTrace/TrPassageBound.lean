/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.Renewal.RnP3
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnP45Mass
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrRaw3Witness
public import CollatzPosDens.StoppingTrace.TrReward
public import CollatzPosDens.StoppingTrace.TrE8Bound
public import CollatzPosDens.StoppingTrace.TrPassageLaw
public import CollatzPosDens.StoppingTrace.TrPassageRaw3
public import CollatzPosDens.StoppingTrace.TrRaw3LastBlock
public import CollatzPosDens.StoppingTrace.TrWitnessWhite

/-!
# One passage from a black point

Fix a level `n`, a unit `ξ ∈ G_n`, and let "white" refer to `(n, ξ, ε_*)`. Let `v ∈ 𝒫` be black
and `s = gap(v)`. Then the tilted mass of one passage of the block path above level `s`, started
from `v`, is at most `1 - d_* - δ_tr(s)`:
```
∑_{π ∈ Π_s} bw^⊗(π) exp(-γ_* N^*(v, π; |π|)) ≤ 1 - d_* - δ_tr(s).
```

The proof splits `Π_s` according to how the last block crosses level `s`. With
`f = ⌊(5s + 16)/16⌋` and `V = {(r, l) : 1 ≤ r ≤ f, s + 1 ≤ l ≤ s + 4}`, let
`𝒜₄₅ = {π ∈ Π_s : Bp_{|π|}(π) ∈ V}`. The passage law gives the masses `∑_{Π_s} bw^⊗ = 1` and
`∑_{𝒜₄₅} bw^⊗ = p₄₅(s)`, and `∑_{𝒜₃(s)} bw^⊗ = p₃(s)`. The sets `𝒜₄₅` and `𝒜₃(s)` are disjoint.
On `𝒜₄₅` the last block ends at the white point `v + Bp_{|π|}(π)`, so its reward is at least `1`;
on `𝒜₃(s)` the last block has a letter `3` landing on a white point, so its reward is at least
`κ_*`. Summing `e^{-γ_* N^*} ≤ 1 - (1 - e^{-γ_*}) 1_{𝒜₄₅} - (1 - e^{-κ_* γ_*}) 1_{𝒜₃(s)}` against
`bw^⊗` and using `E₈(t) < 1 - e^{-t}` for `t > 0` gives the bound.

## Main results

* `CollatzPosDens.summable_trPassage_mul_exp_neg_trCount`: the series converges.
* `CollatzPosDens.tsum_trPassage_mul_exp_neg_trCount_le`: the one-passage bound.

## Implementation notes

The sum over `Π_s` is the real `tsum` over the subtype `trPassage s`; its summability is proved
separately, so the bound is not an artefact of the junk value of a divergent `tsum`. No
hypothesis `n ≥ 1` and no half-level `J = ⌊n/2⌋` is needed. The point `v` is required to lie in
`𝒫` (`v ∈ bkPoints`).

The disjointness of `𝒜₄₅` and `𝒜₃(s)` is argued with the last block `(c, e)` directly: on `𝒜₃(s)`
the raw crossing of level `s` happens at a letter of `c`, and the remaining letters of the block
are nonnegative and the closing letter is at least `4`, so the endpoint lies strictly above
level `s + 4`, outside `V`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.3.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- A real series of nonnegative terms whose `ℝ≥0∞`-valued sum is `ofReal c`, `c ≥ 0`, has sum
`c`. -/
private lemma hasSum_of_tsum_ofReal {α : Type*} {g : α → ℝ} (hg : ∀ a, 0 ≤ g a) {c : ℝ}
    (hc : 0 ≤ c) (h : ∑' a, ENNReal.ofReal (g a) = ENNReal.ofReal c) : HasSum g c := by
  have hne : ∑' a, ENNReal.ofReal (g a) ≠ ⊤ := by rw [h]; exact ENNReal.ofReal_ne_top
  have hs := ENNReal.summable_toReal hne
  simp only [ENNReal.toReal_ofReal (hg _)] at hs
  convert hs.hasSum
  rw [← ENNReal.toReal_ofReal hc, ← h, ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
  simp [ENNReal.toReal_ofReal (hg _)]

/-- The finite set `V = {(r, s + O) : 1 ≤ r ≤ ⌊(5s+16)/16⌋, 1 ≤ O ≤ 4}` of closing exits. -/
private def exitSet (s : ℕ) : Finset (ℤ × ℤ) :=
  (Icc 1 ((5 * s + 16) / 16) ×ˢ Icc (1 : ℤ) 4).image fun p ↦ ((p.1 : ℤ), (s : ℤ) + p.2)

private lemma sum_exitSet (s : ℕ) : ∑ x ∈ exitSet s, firstPassageLaw s x = p45 s := by
  rw [exitSet, sum_image, sum_product]
  · exact sum_firstPassageLaw_eq_p45 s
  · rintro ⟨r, O⟩ - ⟨r', O'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Prod.mk.injEq]
    exact ⟨by exact_mod_cast h1, by omega⟩

/-- The total mass of the passage lists is `1`. -/
private lemma hasSum_trListWeight_trPassage (s : ℕ) :
    HasSum (fun π : trPassage s ↦ trListWeight π.1) 1 := by
  refine hasSum_of_tsum_ofReal (fun π ↦ trListWeight_nonneg _) zero_le_one ?_
  have h := tsum_trPassage_eq_tsum_firstPassageLaw s (fun _ ↦ 1)
  simp only [mul_one] at h
  rw [h, ← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ firstPassageLaw_nonneg _ x)
    (summable_firstPassageLaw s), tsum_firstPassageLaw]

/-- The mass of the closing exits `𝒜₄₅` is `p₄₅(s)`. -/
private lemma hasSum_trListWeight_exitSet (s : ℕ) :
    HasSum (fun π : trPassage s ↦
      if chBlockPath π.1 π.1.length ∈ exitSet s then trListWeight π.1 else 0) (p45 s) := by
  classical
  refine hasSum_of_tsum_ofReal (fun π ↦ by split_ifs <;> simp [trListWeight_nonneg])
    (p45_nonneg s) ?_
  have h := tsum_trPassage_eq_tsum_firstPassageLaw s
    (fun x ↦ if x ∈ exitSet s then 1 else 0)
  have hl : ∀ π : trPassage s, ENNReal.ofReal
      (if chBlockPath π.1 π.1.length ∈ exitSet s then trListWeight π.1 else 0) =
      ENNReal.ofReal (trListWeight π.1) *
        (if chBlockPath π.1 π.1.length ∈ exitSet s then 1 else 0) := by
    intro π; split_ifs <;> simp
  simp_rw [hl]
  rw [h, tsum_eq_sum (s := exitSet s) (fun x hx ↦ by simp [hx]),
    ← sum_exitSet, ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ firstPassageLaw_nonneg _ x)]
  exact sum_congr rfl fun x hx ↦ by simp [hx]

/-- The mass of the raw-three witnesses, as a series over the passage lists. -/
private lemma hasSum_trListWeight_trRawThreeWitness' (s : ℕ) :
    HasSum (fun π : trPassage s ↦ (trRawThreeWitness s).indicator trListWeight π.1) (p3 s) := by
  have h := (hasSum_subtype_iff_indicator (f := trListWeight)).mp
    (hasSum_trListWeight_trRawThreeWitness s)
  refine (hasSum_subtype_iff_indicator
    (f := (trRawThreeWitness s).indicator trListWeight)).mpr ?_
  rwa [Set.indicator_indicator, Set.inter_eq_right.mpr (trRawThreeWitness_subset_trPassage s)]

/-- The sets `𝒜₄₅` and `𝒜₃(s)` are disjoint. -/
private lemma not_mem_exitSet_of_mem_trRawThreeWitness {s : ℕ} {π : List (List ℤ × ℤ)}
    (hπ : π ∈ trRawThreeWitness s) : chBlockPath π π.length ∉ exitSet s := by
  intro hV
  have hP := trRawThreeWitness_mem_trPassage hπ
  have hlt := trRawThreeWitness_lt_trRawSum hπ
  obtain ⟨π₀, ⟨c, e⟩, rfl⟩ :=
    (List.eq_nil_or_concat' π).resolve_left (ne_nil_of_mem_trPassage hP)
  obtain ⟨i, -, hic, -, hI⟩ := trRawThreeWitness_lastBlock hπ (List.getLast?_concat)
  have he : e ∈ ({4, 5} : Set ℤ) := trPassage_closing_mem hP (b := (c, e)) (by simp)
  have hlive := trLive_of_mem_trPassage hP
  have hdrop : 0 ≤ (c.drop i).sum := List.sum_nonneg fun x hx ↦
    zero_le_two.trans (two_le_of_chBlockWeight_ne_zero (β := (c, e)) (hlive (c, e) (by simp))
      (List.mem_of_mem_drop hx))
  have hsplit := congrArg List.sum (List.take_append_drop i c)
  rw [List.sum_append] at hsplit
  rw [show (π₀ ++ [(c, e)]).length - 1 = π₀.length by simp] at hI
  have hI2 := congrArg Prod.snd hI
  have hk : (π₀ ++ [(c, e)]).length = π₀.length + 1 := by simp
  have hstep := chBlockPath_succ (π₀ ++ [(c, e)]) (i := π₀.length) (by simp)
  rw [hk, hstep] at hV
  simp only [List.getElem_concat_length, exitSet, mem_image, mem_product, mem_Icc] at hV
  obtain ⟨⟨r, O⟩, ⟨-, -, hO⟩, hpt⟩ := hV
  have h2 := congrArg Prod.snd hpt
  simp only [Prod.snd_add, chBlockPoint_snd] at h2 hI2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  omega

/-- A block whose `i`-th nonclosing letter is a `3` landing on a white point has reward at
least `κ_*`. -/
private lemma kappaStar_le_trReward {n : ℕ} {ξ : ResidueGroup n} {x : ℤ × ℤ} {c : List ℤ}
    {e : ℤ} {i : ℕ} (hi : 1 ≤ i) (hic : i ≤ c.length) (h3 : c[i - 1]? = some 3)
    (hw : IsBkWhite n ξ (epsStar : ℝ) (x + ((i : ℤ), (c.take i).sum))) :
    (kappaStar : ℝ) ≤ trReward n ξ x (c, e) := by
  have hmem : i ∈ (Icc 1 c.length).filter fun i ↦
      c.getD (i - 1) 0 = 3 ∧ IsBkWhite n ξ (epsStar : ℝ) (x + ((i : ℤ), (c.take i).sum)) := by
    simp only [mem_filter, mem_Icc, List.getD_eq_getElem?_getD, h3, Option.getD_some]
    exact ⟨⟨hi, hic⟩, trivial, hw⟩
  have hcard : (1 : ℝ) ≤ (((Icc 1 c.length).filter fun i ↦
      c.getD (i - 1) 0 = 3 ∧
        IsBkWhite n ξ (epsStar : ℝ) (x + ((i : ℤ), (c.take i).sum))).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨i, hmem⟩
  have hk : (0 : ℝ) ≤ kappaStar := by exact_mod_cast kappaStar_nonneg
  rw [trReward_def]
  have : (0 : ℝ) ≤ if IsBkWhite n ξ (epsStar : ℝ) (x + chBlockPoint (c, e)) then 1 else 0 := by
    split_ifs <;> norm_num
  nlinarith

/-- The pointwise bound
`bw^⊗(π) e^{-γ_* N^*} ≤ bw^⊗(π) - (1 - e^{-γ_*}) bw^⊗(π) 1_{𝒜₄₅}
  - (1 - e^{-κ_* γ_*}) bw^⊗(π) 1_{𝒜₃(s)}` for a passage list `π ∈ Π_s`, `s = gap(v)`. -/
private lemma trListWeight_mul_exp_le {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v)
    {π : List (List ℤ × ℤ)} (hπ : π ∈ trPassage (trGap n ξ (epsStar : ℝ) v)) :
    trListWeight π * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length) ≤
      trListWeight π -
        (1 - Real.exp (-(gammaStar : ℝ))) *
          (if chBlockPath π π.length ∈ exitSet (trGap n ξ (epsStar : ℝ) v) then
            trListWeight π else 0) -
        (1 - Real.exp (-((kappaStar * gammaStar : ℚ) : ℝ))) *
          (trRawThreeWitness (trGap n ξ (epsStar : ℝ) v)).indicator trListWeight π := by
  obtain ⟨s, hs⟩ : ∃ s, trGap n ξ (epsStar : ℝ) v = s := ⟨_, rfl⟩
  rw [hs] at hπ ⊢
  have hw0 := trListWeight_nonneg π
  have hγ : (0 : ℝ) < gammaStar := by exact_mod_cast gammaStar_pos
  have hκ : (0 : ℝ) < kappaStar := by exact_mod_cast kappaStar_pos
  obtain ⟨π₀, b, rfl⟩ := (List.eq_nil_or_concat' π).resolve_left (ne_nil_of_mem_trPassage hπ)
  have hk : (π₀ ++ [b]).length = π₀.length + 1 := by simp
  have hN : trReward n ξ (v + chBlockPath (π₀ ++ [b]) π₀.length) b ≤
      trCount n ξ v (π₀ ++ [b]) (π₀ ++ [b]).length := by
    rw [hk, trCount_succ v _ (by simp), ← trPath_eq_add_chBlockPath]
    simp only [List.getElem_concat_length]
    linarith [trCount_nonneg (n := n) (ξ := ξ) v (π₀ ++ [b]) π₀.length]
  have hN0 := trCount_nonneg (n := n) (ξ := ξ) v (π₀ ++ [b]) (π₀ ++ [b]).length
  set N := trCount n ξ v (π₀ ++ [b]) (π₀ ++ [b]).length
  set w := trListWeight (π₀ ++ [b])
  by_cases h3 : π₀ ++ [b] ∈ trRawThreeWitness s
  · have hV := not_mem_exitSet_of_mem_trRawThreeWitness h3
    rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hV), Set.indicator_of_mem h3]
    obtain ⟨c, e⟩ := b
    obtain ⟨i, hi, hic, hi3, hI⟩ := trRawThreeWitness_lastBlock h3 (List.getLast?_concat)
    have hlt := trRawThreeWitness_lt_trRawSum h3
    have hle := trRawThreeWitness_trRawSum_le h3
    have hf := trRawThreeWitness_trFirstRaw_le h3
    have hwhite := isBkWhite_add_of_bkBlack_trGap hξ hv hb
      (r := (trFirstRaw s (π₀ ++ [(c, e)]) : ℤ))
      (O := trRawSum (π₀ ++ [(c, e)]) (trFirstRaw s (π₀ ++ [(c, e)])) - s) (by positivity)
      (by rw [hs]; exact_mod_cast hf) (by omega) (by omega)
    rw [hs, show (s : ℤ) + (trRawSum (π₀ ++ [(c, e)]) (trFirstRaw s (π₀ ++ [(c, e)])) - s) =
      trRawSum (π₀ ++ [(c, e)]) (trFirstRaw s (π₀ ++ [(c, e)])) by ring] at hwhite
    rw [show (π₀ ++ [(c, e)]).length - 1 = π₀.length by simp] at hI
    have hwhite' : IsBkWhite n ξ (epsStar : ℝ)
        (v + chBlockPath (π₀ ++ [(c, e)]) π₀.length + ((i : ℤ), (c.take i).sum)) := by
      rwa [add_assoc, ← hI]
    have hR := kappaStar_le_trReward (e := e) hi hic hi3 hwhite'
    have hexp : Real.exp (-(gammaStar : ℝ) * N) ≤ Real.exp (-((kappaStar * gammaStar : ℚ) : ℝ)) :=
      Real.exp_le_exp.mpr (by push_cast; nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left hexp hw0]
  · rw [Set.indicator_of_notMem h3, mul_zero, sub_zero]
    split_ifs with hV
    · simp only [exitSet, mem_image, mem_product, mem_Icc] at hV
      obtain ⟨⟨r, O⟩, ⟨⟨hr1, hr⟩, hO1, hO4⟩, hpt⟩ := hV
      have hwhite := isBkWhite_add_of_bkBlack_trGap hξ hv hb (r := (r : ℤ)) (O := O)
        (by positivity) (by rw [hs]; exact_mod_cast hr) hO1 hO4
      simp only at hpt
      rw [hs, hpt, hk, chBlockPath_succ _ (by simp)] at hwhite
      simp only [List.getElem_concat_length, ← add_assoc] at hwhite
      have hR := one_le_trReward (n := n) (ξ := ξ) _ _ hwhite
      have hexp : Real.exp (-(gammaStar : ℝ) * N) ≤ Real.exp (-(gammaStar : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left hexp hw0]
    · have hexp : Real.exp (-(gammaStar : ℝ) * N) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left hexp hw0]

/-- The tilted passage series `∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}` converges, for any
base point `v` and level `s`. -/
theorem summable_trPassage_mul_exp_neg_trCount {n : ℕ} (ξ : ResidueGroup n) (v : ℤ × ℤ)
    (s : ℕ) :
    Summable fun π : trPassage s ↦
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) := by
  have hγ : (0 : ℝ) < gammaStar := by exact_mod_cast gammaStar_pos
  refine (hasSum_trListWeight_trPassage s).summable.of_nonneg_of_le
    (fun π ↦ mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le) fun π ↦ ?_
  refine mul_le_of_le_one_right (trListWeight_nonneg _) (Real.exp_le_one_iff.mpr ?_)
  nlinarith [trCount_nonneg (n := n) (ξ := ξ) v π.1 π.1.length]

/-- **One passage from a black point.** Let `ξ ∈ G_n` be a unit, `v ∈ 𝒫` black (at the colour
scale `ε_*`) and `s = gap(v)`. Then
`∑_{π ∈ Π_s} bw^⊗(π) exp(-γ_* N^*(v, π; |π|)) ≤ 1 - d_* - δ_tr(s)`. -/
@[collatz_pos_dens "lem_tr_passage_bound"]
theorem tsum_trPassage_mul_exp_neg_trCount_le {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v) :
    ∑' π : trPassage (trGap n ξ (epsStar : ℝ) v),
        trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) ≤
      1 - (dStar : ℝ) - trDelta (trGap n ξ (epsStar : ℝ) v) := by
  set s := trGap n ξ (epsStar : ℝ) v with hs
  set a := 1 - Real.exp (-(gammaStar : ℝ))
  set b := 1 - Real.exp (-((kappaStar * gammaStar : ℚ) : ℝ))
  have hsum := ((hasSum_trListWeight_trPassage s).sub
    ((hasSum_trListWeight_exitSet s).mul_left a)).sub
    ((hasSum_trListWeight_trRawThreeWitness' s).mul_left b)
  have hle := hasSum_le (fun π : trPassage s ↦ trListWeight_mul_exp_le hξ hv hb π.2)
    (summable_trPassage_mul_exp_neg_trCount ξ v s).hasSum hsum
  have hγ : (0 : ℝ) < gammaStar := by exact_mod_cast gammaStar_pos
  have hκγ : (0 : ℝ) < ((kappaStar * gammaStar : ℚ) : ℝ) := by
    exact_mod_cast mul_pos kappaStar_pos gammaStar_pos
  have hE1 := (E8_lt_one_sub_exp_neg hγ).le
  have hE2 := (E8_lt_one_sub_exp_neg hκγ).le
  rw [one_sub_dStar_sub_trDelta]
  nlinarith [mul_le_mul_of_nonneg_right hE1 (p45_nonneg s),
    mul_le_mul_of_nonneg_right hE2 (p3_nonneg s)]

end CollatzPosDens
