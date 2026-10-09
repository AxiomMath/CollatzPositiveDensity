/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpWord
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnHoldSupport

/-!
# First-step decomposition of the first-passage law

For every level `s ∈ ℕ` and every point `x ∈ ℤ × ℤ`, the first-passage law satisfies
`F_s(x) = ∑_{h ∈ 𝒫, l(h) > s} η(h) [x = h] + ∑_{h ∈ 𝒫, 1 ≤ l(h) ≤ s} η(h) F_{s - l(h)}(x - h)`.
Indeed, a first-passage word for level `s` either has one letter `h`, which must then satisfy
`l(h) > s`, or it is `h :: t` with `l(h) ≤ s` and `t` a first-passage word for level `s - l(h)`;
and the product weight splits off its first factor. Letters `h ∈ 𝒫` with `η(h) ≠ 0` have
`l(h) ≥ 2 j(h) + 2 ≥ 4`, so the second sum may be restricted to `1 ≤ l(h) ≤ s`.

## Main results

* `CollatzPosDens.firstPassageLaw_eq_first_step`: the first-step decomposition of `F_s(x)`.
* `CollatzPosDens.firstPassageLaw_eq_first_step_tsum_ite`: the value `η(x) [x ∈ 𝒫, l(x) > s]`
  of its first sum.
* `CollatzPosDens.tsum_bkPoints_eq_add`, `CollatzPosDens.tsum_split_le_tsum_bkPoints`: a sum over
  `𝒫` split into the parts `l(h) > s` and `1 ≤ l(h) ≤ s`.

## Implementation notes

All sums are unconditional sums `tsum` of reals over subtypes, and the identity is first proved
for the corresponding sums in `ℝ≥0∞`, where no summability side conditions arise. To transfer it
back to `ℝ`, the `ℝ≥0∞`-valued first-passage law is shown to be finite by strong induction on
the level, using the `ℝ≥0∞` identity itself: the second sum has only finitely many nonzero terms,
each involving a strictly smaller level. Hence no appeal to the finiteness of the set of
contributing words is needed. The Iverson bracket `[x = h]` is written `if x = h then 1 else 0`,
and `η(h)` for `h ∈ 𝒫 ⊆ ℤ × ℤ` is `holdLaw h.1.toNat h.2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open ENNReal

/-- The indicator-weighted terms of `F_s(x)`, as a function on all lists, valued in `ℝ≥0∞`. -/
private noncomputable def fpTerm (s : ℤ) (x : ℤ × ℤ) (h : List (ℤ × ℤ)) : ℝ≥0∞ :=
  if IsFirstPassageWord s h ∧ h.sum = x then ENNReal.ofReal (firstPassageLawWeight h) else 0

/-- The first-passage law in `ℝ≥0∞`, as a sum over all lists. -/
private noncomputable def fpLawE (s : ℤ) (x : ℤ × ℤ) : ℝ≥0∞ := ∑' h, fpTerm s x h

private lemma fpLawE_of_neg {s : ℤ} (hs : s < 0) (x : ℤ × ℤ) : fpLawE s x = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun h ↦ ?_
  rw [fpTerm, ite_eq_right_iff]
  exact fun hh ↦ absurd hh.1.nonneg (not_le.2 hs)

/-- The real first-passage law is the real part of its `ℝ≥0∞` version. -/
private lemma firstPassageLaw_eq_toReal (s : ℤ) (x : ℤ × ℤ) :
    firstPassageLaw s x = (fpLawE s x).toReal := by
  have h1 : fpLawE s x = ∑' h : {h : List (ℤ × ℤ) // IsFirstPassageWord s h ∧ h.sum = x},
      ENNReal.ofReal (firstPassageLawWeight h.1) := by
    rw [fpLawE]
    refine Eq.trans ?_ (tsum_subtype {h : List (ℤ × ℤ) | IsFirstPassageWord s h ∧ h.sum = x}
      (fun h ↦ ENNReal.ofReal (firstPassageLawWeight h))).symm
    congr 1
    ext h
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, fpTerm]
  rw [h1, ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top), firstPassageLaw]
  congr 1
  ext h
  rw [ENNReal.toReal_ofReal (firstPassageLawWeight_nonneg _)]

open Classical in
/-- Splitting a term of `F_s(x)` according to whether the word has one letter. -/
private lemma fpTerm_cons (s : ℤ) (x p : ℤ × ℤ) (t : List (ℤ × ℤ)) :
    fpTerm s x (p :: t) =
      (if t = [] then
        (if p ∈ bkPoints ∧ 0 ≤ s ∧ s < bkL p ∧ p = x then
          ENNReal.ofReal (holdLaw p.1.toNat p.2) else 0)
        else 0) +
      (if p ∈ bkPoints ∧ 0 ≤ s then ENNReal.ofReal (holdLaw p.1.toNat p.2) else 0) *
        fpTerm (s - bkL p) (x - p) t := by
  rcases t with _ | ⟨q, t⟩
  · simp [fpTerm, isFirstPassageWord_singleton_iff, not_isFirstPassageWord_nil, and_assoc]
  · simp only [fpTerm, isFirstPassageWord_cons_cons_iff, List.sum_cons,
      reduceCtorEq, ite_false, zero_add, firstPassageLawWeight_cons]
    have hx : p + (q + t.sum) = x ↔ q + t.sum = x - p := by
      constructor <;> intro h <;> [rw [← h]; rw [h]] <;> abel
    by_cases hc : p ∈ bkPoints ∧ 0 ≤ s
    · simp only [hc, true_and, ite_true, hx]
      split_ifs
      · exact ENNReal.ofReal_mul (holdLaw_nonneg _ _)
      · simp
    · simp only [hc, ite_false, zero_mul, ite_eq_right_iff]
      tauto

open Classical in
/-- The first-step decomposition in `ℝ≥0∞`. -/
private lemma fpLawE_eq (s : ℤ) (x : ℤ × ℤ) :
    fpLawE s x =
      (if x ∈ bkPoints ∧ 0 ≤ s ∧ s < bkL x then ENNReal.ofReal (holdLaw x.1.toNat x.2)
        else 0) +
      ∑' p, (if p ∈ bkPoints ∧ 0 ≤ s then ENNReal.ofReal (holdLaw p.1.toNat p.2) else 0) *
        fpLawE (s - bkL p) (x - p) := by
  rw [fpLawE]
  have hinj : Function.Injective fun q : (ℤ × ℤ) × List (ℤ × ℤ) ↦ q.1 :: q.2 := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [List.cons.injEq] at h
    rw [h.1, h.2]
  have hsupp : Function.support (fpTerm s x) ⊆
      Set.range fun q : (ℤ × ℤ) × List (ℤ × ℤ) ↦ q.1 :: q.2 := by
    intro h hh
    rcases h with _ | ⟨p, t⟩
    · exact absurd (by simp [fpTerm, not_isFirstPassageWord_nil]) hh
    · exact ⟨(p, t), rfl⟩
  rw [← hinj.tsum_eq hsupp]
  rw [ENNReal.tsum_prod (f := fun p t ↦ fpTerm s x (p :: t))]
  simp only [fpTerm_cons]
  simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left]
  congr 1
  rw [tsum_eq_single x]
  · simp only [tsum_ite_eq]
    congr 1
    simp
  · intro p hp
    simp [hp]

/-- A letter `p ∈ 𝒫` with `η(p) ≠ 0` has `l(p) ≥ 2 j(p) + 2`. -/
theorem two_mul_add_two_le_bkL {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (h : holdLaw p.1.toNat p.2 ≠ 0) : 2 * p.1 + 2 ≤ bkL p := by
  have hp' : 1 ≤ p.1 := hp
  have := two_mul_add_two_le_of_holdLaw_ne_zero (by omega) h
  simp only [bkL]
  omega

/-- The `ℝ≥0∞`-valued first-passage law is finite. -/
private lemma fpLawE_ne_top : ∀ (n : ℕ) (s : ℤ), s < n → ∀ x, fpLawE s x ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
    intro s hs x
    rw [fpLawE_of_neg (by exact_mod_cast hs)]
    exact ENNReal.zero_ne_top
  | succ n ih =>
    intro s hs x
    classical
    rw [fpLawE_eq]
    refine ENNReal.add_ne_top.2 ⟨by split_ifs <;> simp, ?_⟩
    rw [tsum_eq_sum (s := Finset.Icc ((1 : ℤ), (0 : ℤ)) (s, s))]
    · refine ENNReal.sum_ne_top.2 fun p _ ↦ ?_
      by_cases hc : p ∈ bkPoints ∧ 0 ≤ s ∧ holdLaw p.1.toNat p.2 ≠ 0
      · have := two_mul_add_two_le_bkL hc.1 hc.2.2
        have hp' : 1 ≤ p.1 := hc.1
        refine ENNReal.mul_ne_top (by split_ifs <;> simp) (ih _ ?_ _)
        push_cast at hs ⊢
        omega
      · have : (if p ∈ bkPoints ∧ 0 ≤ s then ENNReal.ofReal (holdLaw p.1.toNat p.2)
            else 0) = 0 := by
          split_ifs with h
          · have : holdLaw p.1.toNat p.2 = 0 := by tauto
            simp [this]
          · rfl
        rw [this, zero_mul]
        exact ENNReal.zero_ne_top
    · intro p hp
      by_cases hc : p ∈ bkPoints ∧ 0 ≤ s ∧ holdLaw p.1.toNat p.2 ≠ 0
      · have := two_mul_add_two_le_bkL hc.1 hc.2.2
        have hp' : 1 ≤ p.1 := hc.1
        have hneg : s - bkL p < 0 := by
          by_contra hne
          apply hp
          simp only [Finset.mem_Icc, Prod.le_def]
          simp only [bkL] at this hne
          omega
        rw [fpLawE_of_neg hneg, mul_zero]
      · have : (if p ∈ bkPoints ∧ 0 ≤ s then ENNReal.ofReal (holdLaw p.1.toNat p.2)
            else 0) = 0 := by
          split_ifs with h
          · have : holdLaw p.1.toNat p.2 = 0 := by tauto
            simp [this]
          · rfl
        rw [this, zero_mul]

private lemma fpLawE_ne_top' (s : ℤ) (x : ℤ × ℤ) : fpLawE s x ≠ ⊤ :=
  fpLawE_ne_top (s.toNat + 1) s (by omega) x

open Classical in
/-- The first sum in the first-step decomposition of `F_s(x)` is `η(x)` if `x ∈ 𝒫` and
`l(x) > s`, and `0` otherwise. -/
theorem firstPassageLaw_eq_first_step_tsum_ite (s : ℤ) (x : ℤ × ℤ) :
    (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ s < bkL h},
      holdLaw h.1.1.toNat h.1.2 * if x = h.1 then 1 else 0) =
      if x ∈ bkPoints ∧ s < bkL x then holdLaw x.1.toNat x.2 else 0 := by
  split_ifs with hx
  · rw [tsum_eq_single ⟨x, hx⟩]
    · simp
    · intro b hb
      have : x ≠ b.1 := fun h ↦ hb (Subtype.ext h.symm)
      simp [this]
  · convert tsum_zero with h
    have : x ≠ h.1 := fun e ↦ hx (e ▸ h.2)
    simp [this]

/-- **First-step decomposition** of the first-passage law: for every `s ∈ ℕ` and
`x ∈ ℤ × ℤ`,
`F_s(x) = ∑_{h ∈ 𝒫, l(h) > s} η(h) [x = h] + ∑_{h ∈ 𝒫, 1 ≤ l(h) ≤ s} η(h) F_{s - l(h)}(x - h)`,
where `s - l(h)` and `x - h` are differences in `ℤ` and `ℤ × ℤ`. -/
@[collatz_pos_dens "lem_rn_fp_first_step"]
theorem firstPassageLaw_eq_first_step (s : ℕ) (x : ℤ × ℤ) :
    firstPassageLaw s x =
      (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h},
        holdLaw h.1.1.toNat h.1.2 * if x = h.1 then 1 else 0) +
      ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
        holdLaw h.1.1.toNat h.1.2 * firstPassageLaw (s - bkL h) (x - h) := by
  classical
  have hs : (0 : ℤ) ≤ s := by positivity
  have hE := fpLawE_eq s x
  have hfin := fpLawE_ne_top' s x
  rw [hE] at hfin
  obtain ⟨hA, hB⟩ := ENNReal.add_ne_top.1 hfin
  rw [firstPassageLaw_eq_toReal, hE, ENNReal.toReal_add hA hB,
    firstPassageLaw_eq_first_step_tsum_ite]
  congr 1
  · simp only [hs, true_and]
    split_ifs <;> simp [ENNReal.toReal_ofReal (holdLaw_nonneg _ _)]
  · rw [ENNReal.tsum_toReal_eq (fun p ↦ ENNReal.mul_ne_top (by split_ifs <;> simp)
      (fpLawE_ne_top' _ _))]
    refine Eq.trans ?_ (tsum_subtype {p : ℤ × ℤ | p ∈ bkPoints ∧ 1 ≤ bkL p ∧ bkL p ≤ s}
      (fun p ↦ holdLaw p.1.toNat p.2 * firstPassageLaw (s - bkL p) (x - p))).symm
    congr 1
    ext p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hs, and_true, ENNReal.toReal_mul,
      ← firstPassageLaw_eq_toReal]
    by_cases hp : p ∈ bkPoints
    · by_cases hl1 : 1 ≤ bkL p
      · by_cases hl2 : bkL p ≤ s
        · simp [hp, hl1, hl2, ENNReal.toReal_ofReal (holdLaw_nonneg _ _)]
        · have : firstPassageLaw (s - bkL p) (x - p) = 0 := firstPassageLaw_of_neg (by omega) _
          simp [hp, hl2, this]
      · have : holdLaw p.1.toNat p.2 = 0 := by
          by_contra hη
          have := two_mul_add_two_le_bkL hp hη
          have hp' : 1 ≤ p.1 := hp
          omega
        simp [hp, hl1, this]
    · simp [hp]


/-- A letter `p ∈ 𝒫` with `η(p) ≠ 0` has `l(p) ≥ 1`. -/
theorem one_le_bkL_of_holdLaw_ne_zero {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (h : holdLaw p.1.toNat p.2 ≠ 0) : 1 ≤ bkL p := by
  have := two_mul_add_two_le_bkL hp h
  have hp' : 1 ≤ p.1 := hp
  omega

open Classical in
private lemma tsum_split_eq_tsum_indicator (s : ℕ) (G : ℤ × ℤ → ℝ≥0∞) :
    (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, G h) +
      ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}, G h =
      ∑' p, ({h : ℤ × ℤ | h ∈ bkPoints ∧ (s : ℤ) < bkL h}.indicator G p +
        {h : ℤ × ℤ | h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}.indicator G p) := by
  have e₁ : (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, G h) =
      ∑' p, {h : ℤ × ℤ | h ∈ bkPoints ∧ (s : ℤ) < bkL h}.indicator G p :=
    tsum_subtype _ G
  have e₂ : (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}, G h) =
      ∑' p, {h : ℤ × ℤ | h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}.indicator G p :=
    tsum_subtype _ G
  rw [e₁, e₂, ENNReal.tsum_add]

/-- The two parts `l(h) > s` and `1 ≤ l(h) ≤ s` of a sum over `𝒫` are at most the whole sum. -/
theorem tsum_split_le_tsum_bkPoints (s : ℕ) (G : ℤ × ℤ → ℝ≥0∞) :
    (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, G h) +
      ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}, G h ≤
      ∑' p : bkPoints, G p := by
  classical
  rw [tsum_split_eq_tsum_indicator, tsum_subtype bkPoints G]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, mem_bkPoints]
  split_ifs <;> first | (exfalso; omega) | simp

/-- A sum over `𝒫` of terms vanishing off the support of `η` splits according to whether
`l(h) > s` or `1 ≤ l(h) ≤ s`. -/
theorem tsum_bkPoints_eq_add (s : ℕ) {G : ℤ × ℤ → ℝ≥0∞}
    (hG : ∀ h, holdLaw h.1.toNat h.2 = 0 → G h = 0) :
    ∑' h : bkPoints, G h =
      (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, G h) +
        ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}, G h := by
  classical
  refine le_antisymm ?_ (tsum_split_le_tsum_bkPoints s G)
  rw [tsum_split_eq_tsum_indicator, tsum_subtype bkPoints G]
  refine ENNReal.tsum_le_tsum fun h ↦ ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases hP : h ∈ bkPoints
  · by_cases hη : holdLaw h.1.toNat h.2 = 0
    · simp [hG h hη]
    · have h1 := one_le_bkL_of_holdLaw_ne_zero hP hη
      by_cases hl : (s : ℤ) < bkL h
      · simp [hP, hl]
      · simp [hP, hl, show bkL h ≤ s by omega, h1]
  · simp [hP]

end CollatzPosDens
