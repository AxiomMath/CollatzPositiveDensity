/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnCrossE
public import CollatzPosDens.Renewal.RnCrossP
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpRaw
public import CollatzPosDens.Renewal.RnFpRawLem
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldWords
public import CollatzPosDens.Renewal.RnHoldJmarginal
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.Renewal.RnStraddle
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The exact horizontal crossing law

Let `G ≥ 5` and `r ≥ 1` be integers and put `t = G - 4`. The horizontal marginal of the
first-passage law `F_G` at `r` is
`∑_{ℓ ∈ ℤ} F_G(r, ℓ) = e_t(r - 1) + ∑_{j=0}^{r-2} (p_t(j) - e_t(j)) ν₄₅(r - 1 - j)`,
where `e_t` is the boundary weight, `p_t` the straddle weight and `ν₄₅` the geometric law with
parameter `5/16`.

By the raw-word form of the first-passage law, the left side is the total Pascal weight
`∏ ϖ(c_i)` of the words `c ∈ ℤ^r` with letters `≥ 2`, last letter in `{4, 5}`, letter sum
`S_r > G`, and `S_i ≤ G` for every earlier position `i` carrying a letter in `{4, 5}`. Such a word
is sorted by the unique index `j < r` with `S_j ≤ t < S_{j+1}`. For `j = r - 1` the word is a
word of sum `t` followed by the letter `5`, of total weight `ϖ(5) 𝖱(r - 1, t) = e_t(r - 1)`. For
`j ≤ r - 2` the word splits as a straddling prefix of length `j + 1`, other than the ones of
prefix sum `S_j = t` and last letter `5`, followed by a hold word of length `r - 1 - j`; the two
factors weigh `p_t(j) - e_t(j)` and `ν₄₅(r - 1 - j)`.

## Main results

* `CollatzPosDens.hasSum_firstPassageLaw_cross`: the series `∑_{ℓ ∈ ℤ} F_G(r, ℓ)` converges
  unconditionally to `e_t(r - 1) + ∑_{j=0}^{r-2} (p_t(j) - e_t(j)) ν₄₅(r - 1 - j)`.
* `CollatzPosDens.tsum_firstPassageLaw_cross`: the same identity for the `tsum`.

## Implementation notes

The paper [mazur2026] assumes `G ≥ 6`; the identity holds for `G ≥ 5`, which is assumed here. The
level `G` and the length `r` are natural numbers, and `t = G - 4` is truncated subtraction in
`ℕ`, which agrees with the integer difference under `G ≥ 5`. The sum over `ℓ ∈ ℤ` is stated in
the strong (`HasSum`) form. Words are functions `Fin r → ℤ`, a word is split into a prefix and a
suffix by `Fin.appendEquiv`, and the prefix sums `S_n` are sums over the positions `< n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.5.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

private lemma crossLaw_indicator_nonneg {r : ℕ} (s : Set (Fin r → ℤ)) :
    0 ≤ s.indicator varpiWordWeight :=
  fun c ↦ by
    unfold Set.indicator
    split_ifs
    exacts [varpiWordWeight_nonneg c, le_rfl]

/-! ### Summation over fibres -/

/-- Grouping a summable family by the fibres of a map. -/
private lemma crossLaw_hasSum_fiber {β γ : Type*} {g : β → ℝ} (φ : β → γ) {A : ℝ}
    (h : HasSum g A) : HasSum (fun y ↦ ∑' b, ({b | φ b = y} : Set β).indicator g b) A := by
  convert h.tsum_fiberwise φ using 2 with y
  exact (tsum_subtype {b | φ b = y} g).symm

/-- A nonnegative family whose fibre sums form a summable family is summable, with the same
total. -/
private lemma crossLaw_hasSum_of_fiber {β γ : Type*} {g : β → ℝ} (hg : ∀ b, 0 ≤ g b)
    (φ : β → γ) {a : γ → ℝ} {A : ℝ}
    (hfib : ∀ y, HasSum (({b | φ b = y} : Set β).indicator g) (a y)) (ha : HasSum a A) :
    HasSum g A := by
  have hfib' : ∀ y, HasSum (fun b : {b // φ b = y} ↦ g b) (a y) := fun y ↦
    (hasSum_subtype_iff_indicator (s := {b | φ b = y})).2 (hfib y)
  rw [← (Equiv.sigmaFiberEquiv φ).hasSum_iff]
  have hs : Summable (g ∘ Equiv.sigmaFiberEquiv φ) := by
    rw [Function.comp_def, summable_sigma_of_nonneg fun x ↦ hg _]
    refine ⟨fun y ↦ (hfib' y).summable, ?_⟩
    convert ha.summable using 1
    funext y
    exact (hfib' y).tsum_eq
  rw [ha.unique (hs.hasSum.sigma hfib')]
  exact hs.hasSum

/-! ### The three kinds of words -/

/-- The words `c ∈ ℤ^{k+1}` with letters `≥ 2`, `c_1 + ⋯ + c_k = t` and last letter `5`. -/
private def crossLawBnd (t k : ℕ) : Set (Fin (k + 1) → ℤ) :=
  {c | (∀ i, 2 ≤ c i) ∧ ∑ i : Fin k, c i.castSucc = t ∧ c (Fin.last k) = 5}

private lemma crossLawBnd_subset (t k : ℕ) : crossLawBnd t k ⊆ straddleWords t k := by
  rintro c ⟨h2, hs, h5⟩
  refine ⟨h2, hs.le, ?_⟩
  rw [Fin.sum_univ_castSucc, hs, h5]
  omega

private lemma crossLaw_rawMass_mul_varpi_five {t : ℕ} (k : ℕ) (ht : 1 ≤ t) :
    rawMass k t * varpi 5 = boundaryWeight t k := by
  rw [varpi_five]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [rawMass_zero, ite_eq_right (by omega), boundaryWeight_of_nonpos _ (by simp)]
    ring
  · rw [rawMass_eq_choose hk, boundaryWeight_of_pos ht (by omega),
      show ((t : ℤ) - 1).toNat = t - 1 by omega, Int.toNat_natCast, zpow_neg, zpow_natCast]
    ring

/-- The words of sum `t` followed by `5` weigh `e_t(k)`. -/
private lemma crossLaw_hasSum_bnd {t : ℕ} (k : ℕ) (ht : 1 ≤ t) :
    HasSum ((crossLawBnd t k).indicator varpiWordWeight) (boundaryWeight t k) := by
  have hsupp : ∀ c ∉ (rawWords k t).image (fun d ↦ (Fin.snoc d 5 : Fin (k + 1) → ℤ)),
      (crossLawBnd t k).indicator varpiWordWeight c = 0 := by
    intro c hc
    refine Set.indicator_of_notMem (fun h ↦ hc ?_) _
    refine mem_image.2 ⟨Fin.init c, mem_rawWords.2 ⟨fun i ↦ h.1 _, h.2.1⟩, ?_⟩
    rw [show (5 : ℤ) = c (Fin.last k) from h.2.2.symm, Fin.snoc_init_self]
  convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _) hsupp using 1
  rw [sum_image (fun d _ e _ h ↦ by simpa using congrArg Fin.init h)]
  have hval : ∀ d ∈ rawWords k t, (crossLawBnd t k).indicator varpiWordWeight
      (Fin.snoc d 5 : Fin (k + 1) → ℤ) = varpiWordWeight d * varpi 5 := by
    intro d hd
    rw [mem_rawWords] at hd
    rw [Set.indicator_of_mem]
    · simp [varpiWordWeight, Fin.prod_univ_castSucc]
    · refine ⟨fun i ↦ ?_, by simpa using hd.2, by simp⟩
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hd.1 i
  rw [sum_congr rfl hval, ← sum_mul, ← crossLaw_rawMass_mul_varpi_five k ht]
  rfl

/-- The words `c ∈ ℤ^k` that are hold words (of their own letter sum). -/
private def crossLawHold (k : ℕ) : Set (Fin k → ℤ) := {c | c ∈ holdWords k (∑ i, c i)}

/-- The hold words of length `k ≥ 1` weigh `ν₄₅(k)`. -/
private lemma crossLaw_hasSum_hold {k : ℕ} (hk : 1 ≤ k) :
    HasSum ((crossLawHold k).indicator varpiWordWeight) (nu45 k) := by
  refine crossLaw_hasSum_of_fiber (fun c ↦ crossLaw_indicator_nonneg _ c)
    (fun c : Fin k → ℤ ↦ ∑ i, c i) (a := holdLaw k) (fun y ↦ ?_) (hasSum_holdLaw hk)
  have hset : {b : Fin k → ℤ | ∑ i, b i = y} ∩ crossLawHold k = holdWords k y := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, crossLawHold]
    exact ⟨fun ⟨h, h'⟩ ↦ by rwa [h] at h',
      fun h ↦ ⟨holdWords_sum_eq h, by rwa [holdWords_sum_eq h]⟩⟩
  have hfin : ∀ c ∉ rawWords k y, (holdWords k y).indicator varpiWordWeight c = 0 := fun c hc ↦
    Set.indicator_of_notMem (fun h ↦ hc (mem_rawWords.2 ⟨h.1, h.2.2.2⟩)) _
  have hval : ∑' b, (holdWords k y).indicator varpiWordWeight b = holdLaw k y := by
    rw [holdLaw_def, ← _root_.tsum_subtype (holdWords k y)]
  have e : ({b : Fin k → ℤ | ∑ i, b i = y}.indicator fun c ↦ (crossLawHold k).indicator
      varpiWordWeight c) = (holdWords k y).indicator varpiWordWeight := by
    rw [← hset, ← Set.indicator_indicator]
  rw [e, ← hval]
  exact (summable_of_ne_finset_zero (L := SummationFilter.unconditional _) hfin).hasSum

/-! ### The decomposition -/

/-- The raw first-passage words of length `r` for level `G` with letter sum `> G`. -/
private def crossLawD (G r : ℕ) : Set (Fin r → ℤ) :=
  {c | c ∈ firstPassageWords G r (∑ i, c i) ∧ (G : ℤ) < ∑ i, c i}

/-- The words with `S_j ≤ t < S_{j+1}`. -/
private def crossLawA {r : ℕ} (t j : ℕ) : Set (Fin r → ℤ) :=
  {c | wordPrefixSum c j ≤ t ∧ (t : ℤ) < wordPrefixSum c (j + 1)}

private lemma crossLaw_existsUnique_A {r t : ℕ} (c : Fin r → ℤ) (h2 : ∀ i, 2 ≤ c i)
    (ht : (t : ℤ) < ∑ i, c i) :
    ∃ j < r, c ∈ crossLawA t j ∧ ∀ i < r, c ∈ crossLawA t i → i = j := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp at ht
      omega
    · exact hr
  have hex : ∃ n, (t : ℤ) < wordPrefixSum c (n + 1) :=
    ⟨r - 1, by rwa [wordPrefixSum_of_le c (by omega)]⟩
  have hjr : Nat.find hex < r := by
    have := Nat.find_min' hex (m := r - 1) (by rwa [wordPrefixSum_of_le c (by omega)])
    omega
  have hle : ∀ {a b : ℕ}, a ≤ b → b ≤ r → wordPrefixSum c a ≤ wordPrefixSum c b := fun hab hb ↦ by
    have := wordPrefixSum_add_two_mul_le c h2 hab hb
    omega
  have hA : c ∈ crossLawA t (Nat.find hex) := by
    refine ⟨?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, wordPrefixSum_zero]
      omega
    · have := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
      exact not_lt.1 this
  refine ⟨Nat.find hex, hjr, hA, fun i hi hiA ↦ ?_⟩
  obtain ⟨hi1, hi2⟩ := hiA
  obtain ⟨hj1, hj2⟩ := hA
  rcases lt_trichotomy i (Nat.find hex) with h | h | h
  · have := hle (a := i + 1) (b := Nat.find hex) (by omega) (by omega)
    omega
  · exact h
  · have := hle (a := Nat.find hex + 1) (b := i) (by omega) (by omega)
    omega

private lemma crossLawD_inter_A_last {G k : ℕ} (hG : 5 ≤ G) :
    crossLawD G (k + 1) ∩ crossLawA (G - 4) k = crossLawBnd (G - 4) k := by
  ext c
  have hk1 := wordPrefixSum_succ c (n := k) (by omega)
  rw [wordPrefixSum_of_le c le_rfl, wordPrefixSum_last] at hk1
  rw [show c ⟨k, by omega⟩ = c (Fin.last k) from rfl] at hk1
  simp only [crossLawD, crossLawA, crossLawBnd, Set.mem_inter_iff, Set.mem_ofPred_eq,
    mem_firstPassageWords, wordPrefixSum_last, wordPrefixSum_of_le c le_rfl,
    sum_Iic_eq_wordPrefixSum, Set.mem_insert_iff, Set.mem_singleton_iff, true_and]
  constructor
  · rintro ⟨⟨⟨h2, hlast, -⟩, hG'⟩, hA1, hA2⟩
    have := hlast (Fin.last k) (by simp)
    refine ⟨h2, ?_, ?_⟩ <;> omega
  · rintro ⟨h2, hS, h5⟩
    refine ⟨⟨⟨h2, fun i hi ↦ ?_, fun i hi _ ↦ ?_⟩, by omega⟩, by omega, by omega⟩
    · obtain rfl : i = Fin.last k := Fin.ext (by simp; omega)
      exact Or.inr h5
    · have := wordPrefixSum_add_two_mul_le c h2 (a := i + 1) (b := k) (by omega) (by omega)
      rw [wordPrefixSum_last] at this
      omega

/-- In a straddling word other than the boundary ones, every prefix ending in a letter of
`{4, 5}` has sum `≤ G`. -/
private lemma crossLaw_prefixSum_le_of_straddle {G j : ℕ} (hG : 5 ≤ G) {a : Fin (j + 1) → ℤ}
    (h2a : ∀ i, 2 ≤ a i) (hS : ∑ i : Fin j, a i.castSucc ≤ (G - 4 : ℕ))
    (hnB : ¬(∑ i : Fin j, a i.castSucc = (G - 4 : ℕ) ∧ a (Fin.last j) = 5)) (i : Fin (j + 1))
    (h45 : a i = 4 ∨ a i = 5) : wordPrefixSum a (i + 1) ≤ G := by
  by_cases hij : (i : ℕ) < j
  · have := wordPrefixSum_add_two_mul_le a h2a (a := i + 1) (b := j) (by omega) (by omega)
    rw [wordPrefixSum_last] at this
    omega
  · obtain rfl : i = Fin.last j := Fin.ext (by simp; omega)
    rw [Fin.val_last, wordPrefixSum_of_le a le_rfl, Fin.sum_univ_castSucc]
    omega

/-- Once a prefix sum exceeds `G - 4`, appending a nonempty prefix of a word with letters `≥ 2`
ending in a letter of `{4, 5}` pushes it past `G`. -/
private lemma crossLaw_lt_add_prefixSum {G m : ℕ} {s : ℤ} (hs : ((G - 4 : ℕ) : ℤ) < s)
    {b : Fin (m + 1) → ℤ} (h2b : ∀ i, 2 ≤ b i) (i : Fin (m + 1)) (hi : (i : ℕ) + 1 < m + 1)
    (hb : b i = 4 ∨ b i = 5) : (G : ℤ) < s + wordPrefixSum b (i + 1) := by
  rw [wordPrefixSum_succ b (n := i) (by omega), Fin.eta]
  have := wordPrefixSum_nonneg b h2b i
  omega

private lemma crossLaw_append_mem {G j m : ℕ} (hG : 5 ≤ G) (a : Fin (j + 1) → ℤ)
    (b : Fin (m + 1) → ℤ) :
    Fin.append a b ∈ crossLawD G (j + 1 + (m + 1)) ∩ crossLawA (G - 4) j ↔
      a ∈ straddleWords (G - 4) j \ crossLawBnd (G - 4) j ∧ b ∈ crossLawHold (m + 1) := by
  have hPj : wordPrefixSum (Fin.append a b) j = ∑ i : Fin j, a i.castSucc := by
    rw [wordPrefixSum_append_of_le a b (by omega), wordPrefixSum_last]
  have hPj1 : wordPrefixSum (Fin.append a b) (j + 1) = ∑ i, a i := by
    rw [wordPrefixSum_append_of_le a b le_rfl, wordPrefixSum_of_le a le_rfl]
  have hsum : ∑ i, Fin.append a b i = ∑ i, a i + ∑ i, b i := by simp [Fin.sum_univ_add]
  have haS : ∑ i, a i = ∑ i : Fin j, a i.castSucc + a (Fin.last j) := Fin.sum_univ_castSucc a
  have hbS : ∑ i, b i = ∑ i : Fin m, b i.castSucc + b (Fin.last m) := Fin.sum_univ_castSucc b
  simp only [crossLawD, crossLawA, crossLawBnd, crossLawHold, straddleWords, Set.mem_inter_iff,
    Set.mem_sdiff, Set.mem_ofPred_eq, mem_firstPassageWords, mem_holdWords,
    sum_Iic_eq_wordPrefixSum, hPj, hPj1, hsum, Set.mem_insert_iff, Set.mem_singleton_iff,
    true_and, and_true]
  constructor
  · rintro ⟨⟨⟨h2, hlast, hpre⟩, hG'⟩, hA1, hA2⟩
    have h2a : ∀ i, 2 ≤ a i := fun i ↦ by simpa using h2 (Fin.castAdd _ i)
    have h2b : ∀ i, 2 ≤ b i := fun i ↦ by simpa using h2 (Fin.natAdd _ i)
    refine ⟨⟨⟨h2a, hA1, hA2⟩, ?_⟩, h2b, fun i hi hb ↦ ?_, fun i hi ↦ ?_⟩
    · rintro ⟨-, hS, h5⟩
      have := hpre (Fin.castAdd (m + 1) (Fin.last j)) (by simp) (by simp [h5])
      simp only [Fin.val_castAdd, Fin.val_last, hPj1] at this
      omega
    · have := hpre (Fin.natAdd (j + 1) i) (by simp; omega) (by simpa using hb)
      simp only [Fin.val_natAdd] at this
      rw [wordPrefixSum_append_of_ge a b (by omega),
        show j + 1 + (i : ℕ) + 1 - (j + 1) = i + 1 by omega] at this
      exact absurd this (not_le.2 (crossLaw_lt_add_prefixSum hA2 h2b i hi hb))
    · simpa using hlast (Fin.natAdd (j + 1) i) (by simp; omega)
  · rintro ⟨⟨⟨h2a, hS1, hS2⟩, hnB⟩, h2b, hbn, hbl⟩
    refine ⟨⟨⟨fun i ↦ ?_, fun i hi ↦ ?_, fun i hi h45 ↦ ?_⟩, ?_⟩, hS1, hS2⟩
    · induction i using Fin.addCases with
      | left i => simpa using h2a i
      | right i => simpa using h2b i
    · induction i using Fin.addCases with
      | left i => exact absurd hi (by simp only [Fin.val_castAdd]; omega)
      | right i => simpa using hbl i (by simp only [Fin.val_natAdd] at hi; omega)
    · induction i using Fin.addCases with
      | left i =>
        simp only [Fin.val_castAdd, Fin.append_left] at hi h45 ⊢
        rw [wordPrefixSum_append_of_le a b (by omega)]
        exact crossLaw_prefixSum_le_of_straddle hG h2a hS1 (fun h ↦ hnB ⟨h2a, h⟩) i h45
      | right i =>
        simp only [Fin.val_natAdd, Fin.append_right] at hi h45
        exact absurd h45 (hbn i (by omega))
    · have h0 : 0 ≤ ∑ i : Fin m, b i.castSucc :=
        sum_nonneg fun i _ ↦ by linarith [h2b i.castSucc]
      have := hbl (Fin.last m) (by simp)
      omega

private lemma crossLaw_hasSum_mid {G j m : ℕ} (hG : 5 ≤ G) :
    HasSum ((crossLawD G (j + 1 + (m + 1)) ∩ crossLawA (G - 4) j).indicator varpiWordWeight)
      ((straddleWeight (G - 4) j - boundaryWeight (G - 4) j) * nu45 ((m : ℤ) + 1)) := by
  rw [← (Fin.appendEquiv (j + 1) (m + 1)).hasSum_iff]
  have hS : HasSum ((straddleWords (G - 4) j \ crossLawBnd (G - 4) j).indicator varpiWordWeight)
      (straddleWeight (G - 4) j - boundaryWeight (G - 4) j) := by
    rw [Set.indicator_sdiff (crossLawBnd_subset _ _)]
    exact (hasSum_straddleWords _ _).sub (crossLaw_hasSum_bnd _ (by omega))
  have hH := crossLaw_hasSum_hold (k := m + 1) (by omega)
  push_cast at hH
  convert hS.mul hH (hS.summable.mul_of_nonneg hH.summable (crossLaw_indicator_nonneg _)
    (crossLaw_indicator_nonneg _)) using 1
  funext p
  obtain ⟨a, b⟩ := p
  have he : Fin.appendEquiv (j + 1) (m + 1) (a, b) = Fin.append a b :=
    funext fun i ↦ Fin.appendEquiv_apply _ _ _ i
  simp only [Function.comp_apply, he]
  by_cases h : a ∈ straddleWords (G - 4) j \ crossLawBnd (G - 4) j ∧ b ∈ crossLawHold (m + 1)
  · rw [Set.indicator_of_mem ((crossLaw_append_mem hG a b).2 h), Set.indicator_of_mem h.1,
      Set.indicator_of_mem h.2]
    simp [varpiWordWeight, Fin.prod_univ_add]
  · rw [Set.indicator_of_notMem (fun h' ↦ h ((crossLaw_append_mem hG a b).1 h'))]
    by_cases ha : a ∈ straddleWords (G - 4) j \ crossLawBnd (G - 4) j
    · rw [Set.indicator_of_notMem (s := crossLawHold (m + 1)) (fun hb ↦ h ⟨ha, hb⟩), mul_zero]
    · rw [Set.indicator_of_notMem ha, zero_mul]

/-! ### The crossing law -/

/-- The words of `crossLawD G r` are partitioned by the index `j < r` with
`S_j ≤ G - 4 < S_{j+1}`. -/
private lemma crossLawD_indicator_eq_sum (G r : ℕ) (c : Fin r → ℤ) :
    (crossLawD G r).indicator varpiWordWeight c =
      ∑ j ∈ range r, (crossLawD G r ∩ crossLawA (G - 4) j).indicator varpiWordWeight c := by
  by_cases hc : c ∈ crossLawD G r
  · obtain ⟨j, hj, hjA, huniq⟩ := crossLaw_existsUnique_A (t := G - 4) c
      (firstPassageWords_two_le hc.1) (by have := hc.2; omega)
    rw [sum_eq_single_of_mem j (mem_range.2 hj) (fun i hi hij ↦ Set.indicator_of_notMem
      (fun h ↦ hij (huniq i (mem_range.1 hi) h.2)) _), Set.indicator_of_mem
      (show c ∈ crossLawD G r ∩ crossLawA (G - 4) j from ⟨hc, hjA⟩),
      Set.indicator_of_mem hc]
  · rw [Set.indicator_of_notMem hc,
      sum_eq_zero fun j _ ↦ Set.indicator_of_notMem (fun h ↦ hc h.1) _]

/-- The fibre of `crossLawD G r` over the letter sum `ℓ` weighs `F_G(r, ℓ)`. -/
private lemma crossLaw_firstPassageLaw_eq_tsum {G r : ℕ} (hr : 1 ≤ r) (ℓ : ℤ) :
    firstPassageLaw G (r, ℓ) =
      ∑' c, ({b : Fin r → ℤ | ∑ i, b i = ℓ} ∩ crossLawD G r).indicator varpiWordWeight c := by
  by_cases hℓ : (G : ℤ) < ℓ
  · have hset : {b : Fin r → ℤ | ∑ i, b i = ℓ} ∩ crossLawD G r = firstPassageWords G r ℓ := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, crossLawD, mem_coe]
      refine ⟨fun ⟨h, h', _⟩ ↦ by rwa [h] at h', fun h ↦ ?_⟩
      have hs := firstPassageWords_sum_eq h
      exact ⟨hs, by rwa [hs], by rwa [hs]⟩
    rw [hset, firstPassageLaw_eq_sum_firstPassageWords G r hr ℓ hℓ,
      tsum_eq_sum (s := firstPassageWords G r ℓ) fun c hc ↦ Set.indicator_of_notMem
        (by simpa using hc) _]
    exact sum_congr rfl fun c hc ↦ (Set.indicator_of_mem (mem_coe.2 hc) varpiWordWeight).symm
  · have hset : {b : Fin r → ℤ | ∑ i, b i = ℓ} ∩ crossLawD G r = ∅ := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, crossLawD, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h _ h'
      omega
    rw [hset, Set.indicator_empty, tsum_zero]
    by_contra hne
    exact hℓ (firstPassageLaw_support hne).2

/-- **Exact horizontal crossing law.** For integers `G ≥ 5` and `r ≥ 1`, with `t = G - 4`,
`∑_{ℓ ∈ ℤ} F_G(r, ℓ) = e_t(r - 1) + ∑_{j=0}^{r-2} (p_t(j) - e_t(j)) ν₄₅(r - 1 - j)`, the series
converging unconditionally. -/
@[collatz_pos_dens "lem_rn_cross_law"]
theorem hasSum_firstPassageLaw_cross {G r : ℕ} (hG : 5 ≤ G) (hr : 1 ≤ r) :
    HasSum (fun ℓ : ℤ ↦ firstPassageLaw G (r, ℓ))
      (boundaryWeight (G - 4) ((r : ℤ) - 1) +
        ∑ j ∈ range (r - 1), (straddleWeight (G - 4) j - boundaryWeight (G - 4) j) *
          nu45 ((r : ℤ) - 1 - j)) := by
  set v : ℕ → ℝ := fun j ↦ if j + 1 = r then boundaryWeight (G - 4) j else
    (straddleWeight (G - 4) j - boundaryWeight (G - 4) j) * nu45 ((r : ℤ) - 1 - j) with hv
  have hpiece : ∀ j ∈ range r,
      HasSum ((crossLawD G r ∩ crossLawA (G - 4) j).indicator varpiWordWeight) (v j) := by
    intro j hj
    rw [mem_range] at hj
    by_cases hjr : j + 1 = r
    · subst hjr
      rw [crossLawD_inter_A_last hG]
      simpa [hv] using crossLaw_hasSum_bnd j (t := G - 4) (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = j + 1 + (m + 1) := ⟨r - j - 2, by omega⟩
      have hvj : v j = (straddleWeight (G - 4) j - boundaryWeight (G - 4) j) *
          nu45 ((m : ℤ) + 1) := by
        rw [hv]
        dsimp only
        rw [ite_eq_right hjr]
        congr 2
        push_cast
        ring
      rw [hvj]
      exact crossLaw_hasSum_mid hG
  have hD : HasSum ((crossLawD G r).indicator varpiWordWeight) (∑ j ∈ range r, v j) := by
    convert hasSum_sum hpiece using 1
    exact funext (crossLawD_indicator_eq_sum G r)
  have hval : ∑ j ∈ range r, v j = boundaryWeight (G - 4) ((r : ℤ) - 1) +
      ∑ j ∈ range (r - 1), (straddleWeight (G - 4) j - boundaryWeight (G - 4) j) *
        nu45 ((r : ℤ) - 1 - j) := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    rw [sum_range_succ, add_comm, Nat.add_sub_cancel, hv]
    dsimp only
    rw [ite_eq_left rfl, show ((k + 1 : ℕ) : ℤ) - 1 = k by omega]
    congr 1
    exact sum_congr rfl fun j hj ↦ ite_eq_right (by grind)
  rw [← hval]
  convert crossLaw_hasSum_fiber (fun c : Fin r → ℤ ↦ ∑ i, c i) hD using 1
  funext ℓ
  rw [Set.indicator_indicator]
  exact crossLaw_firstPassageLaw_eq_tsum hr ℓ

/-- **Exact horizontal crossing law**, as a `tsum`. -/
theorem tsum_firstPassageLaw_cross {G r : ℕ} (hG : 5 ≤ G) (hr : 1 ≤ r) :
    ∑' ℓ : ℤ, firstPassageLaw G (r, ℓ) =
      boundaryWeight (G - 4) ((r : ℤ) - 1) +
        ∑ j ∈ range (r - 1), (straddleWeight (G - 4) j - boundaryWeight (G - 4) j) *
          nu45 ((r : ℤ) - 1 - j) :=
  (hasSum_firstPassageLaw_cross hG hr).tsum_eq

end CollatzPosDens
