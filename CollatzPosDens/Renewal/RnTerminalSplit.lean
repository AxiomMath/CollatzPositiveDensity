/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.List.OfFn
public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpWord
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnGreen
public import CollatzPosDens.Renewal.RnGreenFinite
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnHoldSupport

/-!
# Splitting off the terminal step of a first passage

Let `s ∈ ℕ` and `(r, ℓ) ∈ ℤ × ℤ` with `ℓ > s`. Splitting a first-passage word `h = h' h_K` for
level `s` with sum `(r, ℓ)` at its last letter `h_K = (q + 1, ℓ - s + p)` (with `q ≥ 0` and
`0 ≤ p ≤ s`) gives
`F_s(r, ℓ) = ∑_{q ≥ 0} ∑_{p = 0}^{s} η(q + 1, ℓ - s + p) 𝒢(r - q - 1, s - p)`.
Indeed, for a word of nonzero weight every letter `(j, l) ∈ 𝒫` has `l ≥ 2j + 2 ≥ 4`
(`two_mul_add_two_le_of_holdLaw_ne_zero`), so the vertical partial sums increase. The prefix
`h'` of a first-passage word therefore has vertical sum in `[0, s]`, and conversely any word `h'`
of nonzero weight with sum `(r - q - 1, s - p)` extends by `(q + 1, ℓ - s + p)` to a
first-passage word for `s` with sum `(r, ℓ)`. The weight is multiplicative under this
concatenation, and summing over `h'` for fixed `(q, p)` gives `η(q + 1, ℓ - s + p)` times the
Green's function `𝒢(r - q - 1, s - p)`.

## Main results

* `CollatzPosDens.firstPassageLaw_eq_tsum_sum_holdLaw_mul_green`: the terminal-step
  decomposition of the first-passage law.

## Implementation notes

The Green's function sums over pairs `(N, h)` with `h : Fin N → ℕ × ℤ`, while the first-passage
law sums over lists of points of `ℤ × ℤ`; the two are matched by `h ↦ List.ofFn h`, with the
first coordinates cast to `ℤ`. All sums are `tsum`s of nonnegative reals. The identity is proved
in `ℝ≥0∞`, where the double sum on the right becomes a single sum over a sigma type, matched with
the first-passage words by appending the last letter. The finiteness of the right-hand side
(`green_finite_support`, and the vanishing of `η(q + 1, ℓ - s + p)` for `q ≥ ℓ`) then gives
the summability of the family defining `F_s(r, ℓ)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.4.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The weight of a word is the product of `η` over its letters. -/
private theorem firstPassageLawWeight_eq_prod (h : List (ℤ × ℤ)) :
    firstPassageLawWeight h = (h.map fun a ↦ holdLaw a.1.toNat a.2).prod := by
  induction h with
  | nil => simp
  | cons a t ih => simp [ih]

/-- The weight of a word is multiplicative under concatenation. -/
private theorem firstPassageLawWeight_append (u v : List (ℤ × ℤ)) :
    firstPassageLawWeight (u ++ v) = firstPassageLawWeight u * firstPassageLawWeight v := by
  simp [firstPassageLawWeight_eq_prod]

/-- The weight of a one-letter word. -/
private theorem firstPassageLawWeight_singleton (a : ℤ × ℤ) :
    firstPassageLawWeight [a] = holdLaw a.1.toNat a.2 := by
  simp

/-- The weight of the word `List.ofFn h` of a tuple `h : Fin N → ℕ × ℤ` (first coordinates cast
to `ℤ`) is the hold-list weight of `h`. -/
private theorem firstPassageLawWeight_ofFn {N : ℕ} (h : Fin N → ℕ × ℤ) :
    firstPassageLawWeight (List.ofFn fun k ↦ (((h k).1 : ℤ), (h k).2)) = holdListLaw h := by
  rw [firstPassageLawWeight_eq_prod, List.map_ofFn, List.prod_ofFn, holdListLaw_def]
  simp

/-- In a word of points of `𝒫` of nonzero weight, every letter has vertical coordinate at
least `4`. -/
private lemma four_le_snd_of_weight_ne_zero {h : List (ℤ × ℤ)} (hP : ∀ a ∈ h, a ∈ bkPoints)
    (hw : firstPassageLawWeight h ≠ 0) {a : ℤ × ℤ} (ha : a ∈ h) : 4 ≤ a.2 := by
  have h1 : 1 ≤ a.1 := hP a ha
  have hη : holdLaw a.1.toNat a.2 ≠ 0 := fun h0 ↦ hw <| by
    rw [firstPassageLawWeight_eq_prod]
    exact List.prod_eq_zero (List.mem_map.2 ⟨a, ha, h0⟩)
  have := two_mul_add_two_le_of_holdLaw_ne_zero (by omega) hη
  omega

/-- The sum of the word `List.ofFn h` of a tuple `h : Fin N → ℕ × ℤ`. -/
private lemma sum_ofFn_cast {N : ℕ} (h : Fin N → ℕ × ℤ) :
    (List.ofFn fun k ↦ (((h k).1 : ℤ), (h k).2)).sum = (∑ k, ((h k).1 : ℤ), ∑ k, (h k).2) := by
  rw [List.sum_ofFn]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

/-- A word of points of `𝒫` is the word `List.ofFn t` of a tuple `t : Fin N → ℕ × ℤ` with
positive first coordinates. -/
private lemma exists_ofFn_eq_of_mem_bkPoints {h : List (ℤ × ℤ)} (hP : ∀ a ∈ h, a ∈ bkPoints) :
    ∃ t : Fin h.length → ℕ × ℤ, (∀ i, 1 ≤ (t i).1) ∧
      (List.ofFn fun k ↦ (((t k).1 : ℤ), (t k).2)) = h := by
  have hk : ∀ k, 1 ≤ (h.get k).1 := fun k ↦ by
    have := hP _ (List.get_mem h k)
    rwa [mem_bkPoints_mk] at this
  refine ⟨fun k ↦ ((h.get k).1.toNat, (h.get k).2), fun k ↦ ?_, ?_⟩
  · have := hk k
    change 1 ≤ (h.get k).1.toNat
    omega
  · conv_rhs => rw [← List.ofFn_get h]
    congr 1
    funext k
    have := hk k
    ext
    · simp only
      omega
    · rfl

/-- **The Green's function as a sum over words.** In `ℝ≥0∞`, `𝒢(j, s)` is the sum of the
weights of the words of points of `𝒫` with sum `(j, s)`. -/
private theorem ofReal_green_eq_tsum_firstPassageLawWeight (j s : ℤ) :
    ENNReal.ofReal (green j s) =
      ∑' h : {h : List (ℤ × ℤ) // (∀ a ∈ h, a ∈ bkPoints) ∧ h.sum = (j, s)},
        ENNReal.ofReal (firstPassageLawWeight h.1) := by
  let S := fun N : ℕ ↦ {h : Fin N → ℕ × ℤ //
    (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s}
  rw [green_def, ENNReal.ofReal_tsum_of_nonneg
    (fun N ↦ tsum_nonneg fun h ↦ holdListLaw_nonneg _)
    (summable_of_hasFiniteSupport (green_finite_support_outer j s))]
  calc ∑' N, ENNReal.ofReal (∑' h : S N, holdListLaw h.1)
      = ∑' N, ∑' h : S N, ENNReal.ofReal (holdListLaw h.1) :=
        tsum_congr fun N ↦ ENNReal.ofReal_tsum_of_nonneg (fun h ↦ holdListLaw_nonneg _)
          (summable_of_hasFiniteSupport (green_finite_support j s N))
    _ = ∑' x : Σ N, S N, ENNReal.ofReal (holdListLaw x.2.1) :=
        (ENNReal.tsum_sigma' (fun x : Σ N, S N ↦ ENNReal.ofReal (holdListLaw x.2.1))).symm
    _ = _ := by
      symm
      refine tsum_eq_tsum_of_ne_zero_bij
        (fun x ↦ ⟨List.ofFn fun k ↦ (((x.1.2.1 k).1 : ℤ), (x.1.2.1 k).2), ?_, ?_⟩) ?_ ?_ ?_
      · intro a ha
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ha
        rw [mem_bkPoints_mk]
        exact_mod_cast x.1.2.2.1 k
      · rw [sum_ofFn_cast, x.1.2.2.2.1, x.1.2.2.2.2]
      · rintro ⟨⟨N₁, h₁, hh₁⟩, hx₁⟩ ⟨⟨N₂, h₂, hh₂⟩, hx₂⟩ heq
        simp only [Subtype.mk.injEq] at heq
        obtain ⟨rfl, heq⟩ := Sigma.mk.inj (List.ofFn_inj'.1 heq)
        obtain rfl : h₁ = h₂ := funext fun k ↦ natCast_prod_injective (congrFun (eq_of_heq heq) k)
        rfl
      · rintro ⟨h, hP, hs⟩ hne
        obtain ⟨t, htP, ht⟩ := exists_ofFn_eq_of_mem_bkPoints hP
        have hsum := sum_ofFn_cast t
        rw [ht, hs] at hsum
        refine ⟨⟨⟨h.length, t, htP, (congrArg Prod.fst hsum).symm,
          (congrArg Prod.snd hsum).symm⟩, ?_⟩, Subtype.ext ht⟩
        simp only [Function.mem_support, ne_eq] at hne ⊢
        rwa [← firstPassageLawWeight_ofFn, ht]
      · rintro ⟨⟨N, h, hh⟩, hx⟩
        exact congrArg ENNReal.ofReal (firstPassageLawWeight_ofFn h)

/-- In a word of points of `𝒫` of nonzero weight, every vertical coordinate is nonnegative. -/
private lemma bkL_nonneg_of_weight_ne_zero {h : List (ℤ × ℤ)} (hP : ∀ a ∈ h, a ∈ bkPoints)
    (hw : firstPassageLawWeight h ≠ 0) : ∀ y ∈ h.map bkL, 0 ≤ y := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
  have := four_le_snd_of_weight_ne_zero hP hw ha
  change 0 ≤ a.2
  linarith

/-- Appending a letter `(q + 1, ℓ - s + p)`, with `s < ℓ`, to a word `h'` of points of `𝒫` of
nonzero weight with sum `(r - q - 1, s - p)` gives a first-passage word for `s` with sum
`(r, ℓ)`. -/
private lemma isFirstPassageWord_append_terminal {s : ℕ} {r ℓ : ℤ} (hℓ : (s : ℤ) < ℓ)
    {q p : ℕ} {h' : List (ℤ × ℤ)} (hP : ∀ a ∈ h', a ∈ bkPoints)
    (hsum : h'.sum = (r - q - 1, (s : ℤ) - (p : ℤ))) (hh' : firstPassageLawWeight h' ≠ 0) :
    IsFirstPassageWord s (h' ++ [((q : ℤ) + 1, ℓ - s + p)]) ∧
      (h' ++ [((q : ℤ) + 1, ℓ - s + p)]).sum = (r, ℓ) := by
  have hsnd : (h'.map bkL).sum = s - p := by
    rw [← bkL_list_sum, hsum]
  have hnn := bkL_nonneg_of_weight_ne_zero hP hh'
  refine ⟨⟨by simp, ?_, fun k hk ↦ ?_, ?_⟩, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hP a ha
    · rw [List.mem_singleton.1 ha, mem_bkPoints_mk]
      omega
  · simp only [List.length_append, List.length_singleton] at hk
    rw [List.take_append_of_le_length (by omega)]
    have := (List.take_sublist k (h'.map bkL)).sum_le_sum hnn
    rw [← List.map_take] at this
    omega
  · simp only [List.map_append, List.sum_append, hsnd, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, bkL]
    omega
  · rw [List.sum_append, hsum]
    simp only [List.sum_cons, List.sum_nil, add_zero, Prod.mk_add_mk]
    ext <;> simp

/-- A first-passage word for `s` with sum `(r, ℓ)` and nonzero weight splits at its last letter
as `h' ++ [(q + 1, ℓ - s + p)]` with `p ≤ s`, where `h'` is a word of points of `𝒫` of nonzero
weight with sum `(r - q - 1, s - p)`. -/
private lemma exists_terminal_decomp {s : ℕ} {r ℓ : ℤ} {h : List (ℤ × ℤ)}
    (hFP : IsFirstPassageWord s h) (hsum : h.sum = (r, ℓ)) (hh : firstPassageLawWeight h ≠ 0) :
    ∃ (q p : ℕ) (_ : p < s + 1) (h' : List (ℤ × ℤ)), (∀ a ∈ h', a ∈ bkPoints) ∧
      h'.sum = (r - q - 1, (s : ℤ) - (p : ℤ)) ∧ firstPassageLawWeight h' ≠ 0 ∧
      holdLaw (q + 1) (ℓ - s + p) ≠ 0 ∧ h' ++ [((q : ℤ) + 1, ℓ - s + p)] = h := by
  have hP : ∀ p ∈ h, p ∈ bkPoints := fun p hp ↦ hFP.mem_bkPoints hp
  set a := h.getLast hFP.ne_nil
  set h' := h.dropLast
  have hdec : h' ++ [a] = h := List.dropLast_append_getLast hFP.ne_nil
  have ha : a ∈ h := List.getLast_mem _
  have hP' : ∀ p ∈ h', p ∈ bkPoints := fun p hp ↦ hP p (List.mem_of_mem_dropLast hp)
  have hw : firstPassageLawWeight h' * holdLaw a.1.toNat a.2 ≠ 0 := by
    rwa [← firstPassageLawWeight_singleton, ← firstPassageLawWeight_append, hdec]
  have hh' : firstPassageLawWeight h' ≠ 0 := left_ne_zero_of_mul hw
  have ha0 : holdLaw a.1.toNat a.2 ≠ 0 := right_ne_zero_of_mul hw
  have ha1 : 1 ≤ a.1 := hP a ha
  have hle : (h'.map bkL).sum ≤ s := by
    have := hFP.sum_take_le (k := h'.length) (by rw [← hdec]; simp)
    rwa [← hdec, List.take_left] at this
  have hnn : 0 ≤ (h'.map bkL).sum := List.sum_nonneg (bkL_nonneg_of_weight_ne_zero hP' hh')
  have hs' : h'.sum + a = (r, ℓ) := by
    rw [← hsum, ← hdec, List.sum_append]
    simp
  have hsnd : (h'.map bkL).sum = h'.sum.2 := (bkL_list_sum h').symm
  have h2 : h'.sum.2 + a.2 = ℓ := congrArg Prod.snd hs'
  have h1 : h'.sum.1 + a.1 = r := congrArg Prod.fst hs'
  set q : ℕ := (a.1 - 1).toNat
  set p : ℕ := (s - h'.sum.2).toNat
  have hq : (q : ℤ) = a.1 - 1 := Int.toNat_of_nonneg (by omega)
  have hp : (p : ℤ) = s - h'.sum.2 := Int.toNat_of_nonneg (by omega)
  have haeq : a = ((q : ℤ) + 1, ℓ - s + p) := by
    ext
    · simp [hq]
    · simp only [hp]
      omega
  have hqa : a.1.toNat = q + 1 := by omega
  refine ⟨q, p, by omega, h', hP', ?_, hh', ?_, ?_⟩
  · ext
    · simp only [hq]
      omega
    · simp only [hp]
      omega
  · rwa [← hqa, show ℓ - s + p = a.2 by rw [haeq]]
  · rw [← haeq, hdec]

/-- The family `q ↦ ∑_{p = 0}^{s} η(q + 1, ℓ - s + p) 𝒢(r - q - 1, s - p)` vanishes for
`q ≥ ℓ`, so it is summable. -/
private lemma summable_sum_holdLaw_mul_green (s : ℕ) (r ℓ : ℤ) :
    Summable fun q : ℕ ↦ ∑ p ∈ Finset.range (s + 1),
      holdLaw (q + 1) (ℓ - s + p) * green (r - q - 1) (s - p) := by
  refine summable_of_ne_finset_zero (s := Finset.range ℓ.toNat) fun q hq ↦ ?_
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have hq' : ℓ ≤ q := by
    simp only [Finset.mem_range, not_lt] at hq
    omega
  have hp' : p ≤ s := by
    simp only [Finset.mem_range] at hp
    omega
  by_contra h0
  have := two_mul_add_two_le_of_holdLaw_ne_zero (by omega) (left_ne_zero_of_mul h0)
  push_cast at this
  omega

/-- In `ℝ≥0∞`, the right-hand side of the terminal-step decomposition is a single sum over the
triples `(q, p, h')` with `h'` a word of points of `𝒫` with sum `(r - q - 1, s - p)`. -/
private lemma ofReal_tsum_sum_holdLaw_mul_green (s : ℕ) (r ℓ : ℤ) :
    ENNReal.ofReal (∑' q : ℕ, ∑ p ∈ Finset.range (s + 1),
      holdLaw (q + 1) (ℓ - s + p) * green (r - q - 1) (s - p)) =
    ∑' x : Σ qp : ℕ × Fin (s + 1), {h : List (ℤ × ℤ) //
        (∀ a ∈ h, a ∈ bkPoints) ∧ h.sum = (r - qp.1 - 1, (s : ℤ) - ((qp.2 : ℕ) : ℤ))},
      ENNReal.ofReal (holdLaw (x.1.1 + 1) (ℓ - s + (x.1.2 : ℕ))) *
        ENNReal.ofReal (firstPassageLawWeight x.2.1) := by
  rw [ENNReal.tsum_sigma', ENNReal.tsum_prod',
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ Finset.sum_nonneg fun _ _ ↦
      mul_nonneg (holdLaw_nonneg _ _) (green_nonneg _ _)) (summable_sum_holdLaw_mul_green s r ℓ)]
  refine tsum_congr fun q ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ mul_nonneg (holdLaw_nonneg _ _) (green_nonneg _ _)),
    Finset.sum_range, tsum_fintype]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [ENNReal.ofReal_mul (holdLaw_nonneg _ _), ofReal_green_eq_tsum_firstPassageLawWeight,
    ← ENNReal.tsum_mul_left]

/-- **Terminal-step decomposition of the first-passage law.** For `s ∈ ℕ`, `r ∈ ℤ` and
`ℓ ∈ ℤ` with `ℓ > s`,
`F_s(r, ℓ) = ∑_{q ≥ 0} ∑_{p = 0}^{s} η(q + 1, ℓ - s + p) 𝒢(r - q - 1, s - p)`. -/
@[collatz_pos_dens "lem_rn_terminal_split"]
theorem firstPassageLaw_eq_tsum_sum_holdLaw_mul_green (s : ℕ) (r ℓ : ℤ) (hℓ : (s : ℤ) < ℓ) :
    firstPassageLaw s (r, ℓ) =
      ∑' q : ℕ, ∑ p ∈ Finset.range (s + 1),
        holdLaw (q + 1) (ℓ - s + p) * green (r - q - 1) (s - p) := by
  let T := Σ qp : ℕ × Fin (s + 1),
    {h : List (ℤ × ℤ) //
      (∀ a ∈ h, a ∈ bkPoints) ∧ h.sum = (r - qp.1 - 1, (s : ℤ) - ((qp.2 : ℕ) : ℤ))}
  let F : T → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (holdLaw (x.1.1 + 1) (ℓ - s + (x.1.2 : ℕ))) *
    ENNReal.ofReal (firstPassageLawWeight x.2.1)
  have hwd : ∀ x : Function.support F,
      IsFirstPassageWord s (x.1.2.1 ++ [((x.1.1.1 : ℤ) + 1, ℓ - s + (x.1.1.2 : ℕ))]) ∧
        (x.1.2.1 ++ [((x.1.1.1 : ℤ) + 1, ℓ - s + (x.1.1.2 : ℕ))]).sum = (r, ℓ) := by
    intro x
    have hx := x.2
    simp only [Function.mem_support, F, ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero, not_or,
      not_le] at hx
    exact isFirstPassageWord_append_terminal hℓ x.1.2.2.1 x.1.2.2.2 hx.2.ne'
  have key : ∑' h : {h : List (ℤ × ℤ) // IsFirstPassageWord s h ∧ h.sum = (r, ℓ)},
      ENNReal.ofReal (firstPassageLawWeight h.1) = ∑' x, F x := by
    refine tsum_eq_tsum_of_ne_zero_bij (fun x ↦ ⟨_, hwd x⟩) ?_ ?_ ?_
    · rintro ⟨⟨⟨q₁, p₁⟩, h₁, hP₁, hs₁⟩, hx₁⟩ ⟨⟨⟨q₂, p₂⟩, h₂, hP₂, hs₂⟩, hx₂⟩ heq
      simp only [Subtype.mk.injEq] at heq
      obtain ⟨rfl, hlast⟩ := List.append_inj' heq rfl
      simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hlast
      obtain ⟨hq, hp⟩ := hlast
      obtain rfl : q₁ = q₂ := by omega
      obtain rfl : p₁ = p₂ := Fin.ext (by omega)
      rfl
    · rintro ⟨h, hFP, hsum⟩ hx
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hx
      obtain ⟨q, p, hps, h', hP', hsum', hh', ha0, hdec⟩ :=
        exists_terminal_decomp hFP hsum hx.ne'
      refine ⟨⟨⟨⟨q, ⟨p, hps⟩⟩, h', hP', hsum'⟩, ?_⟩, Subtype.ext hdec⟩
      simp only [Function.mem_support, ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero, not_or,
        not_le, F]
      exact ⟨(holdLaw_nonneg _ _).lt_of_ne' ha0, (firstPassageLawWeight_nonneg _).lt_of_ne' hh'⟩
    · rintro ⟨⟨⟨q, p⟩, h', hP, hsum⟩, hx⟩
      simp only [F, firstPassageLawWeight_append, firstPassageLawWeight_singleton]
      rw [ENNReal.ofReal_mul (firstPassageLawWeight_nonneg _), mul_comm]
      congr 3
  have hR := ofReal_tsum_sum_holdLaw_mul_green s r ℓ
  have hsum : Summable fun h : {h : List (ℤ × ℤ) // IsFirstPassageWord s h ∧ h.sum = (r, ℓ)} ↦
      firstPassageLawWeight h.1 := by
    have := ENNReal.summable_toReal (key.trans hR.symm ▸ ENNReal.ofReal_ne_top)
    simpa [ENNReal.toReal_ofReal (firstPassageLawWeight_nonneg _)] using this
  refine (ENNReal.ofReal_eq_ofReal_iff (firstPassageLaw_nonneg _ _) (tsum_nonneg fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg (holdLaw_nonneg _ _) (green_nonneg _ _))).1 ?_
  rw [firstPassageLaw, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ firstPassageLawWeight_nonneg _) hsum,
    key, hR]

end CollatzPosDens
