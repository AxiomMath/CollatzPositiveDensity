/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpFinite
public import CollatzPosDens.Renewal.RnFpFirstStep
public import CollatzPosDens.Renewal.RnHoldMass
public import CollatzPosDens.Renewal.RnHoldSupport

/-!
# The total mass of the first-passage law

For every level `s ∈ ℕ`, the first-passage law is a probability distribution on `ℤ × ℤ`:
`∑_{x ∈ ℤ × ℤ} F_s(x) = 1`. The proof is by strong induction on `s`: summing the first-step
decomposition `F_s(x) = ∑_{l(h) > s} η(h) [x = h] + ∑_{1 ≤ l(h) ≤ s} η(h) F_{s - l(h)}(x - h)`
over `x`, translating by `h` and using the induction hypothesis at the level `s - l(h) < s`, gives
`∑_{l(h) > s} η(h) + ∑_{1 ≤ l(h) ≤ s} η(h) = ∑_{h ∈ 𝒫} η(h) = 1`, since `η(h) = 0` when
`l(h) ≤ 0`. In particular each value `F_s(x)` lies in `[0, 1]`.

## Main results

* `CollatzPosDens.hasSum_firstPassageLaw`: `x ↦ F_s(x)` has sum `1`.
* `CollatzPosDens.tsum_firstPassageLaw`: `∑_{x ∈ ℤ × ℤ} F_s(x) = 1`.
* `CollatzPosDens.firstPassageLaw_le_one`: `F_s(x) ≤ 1`.
* `CollatzPosDens.summable_firstPassageLaw_natCast`,
  `CollatzPosDens.tsum_firstPassageLaw_natCast_le_one`,
  `CollatzPosDens.tsum_ofReal_firstPassageLaw_natCast_le_one`: the restriction of `F_s` to
  `ℕ × ℤ` is summable with total mass at most `1` (also as a sum in `[0, ∞]`).

## Implementation notes

The induction is carried out for the images in `ℝ≥0∞` under `ENNReal.ofReal`, where sums of
nonnegative terms can be rearranged without summability side conditions. The real second sum of
the first-step decomposition is summable because, by the induction hypothesis, the values
`F_{s - l(h)}(x - h)` at the smaller levels are at most `1`, so its terms are dominated by `η(h)`.
The total mass being finite then gives summability of the real series. The finiteness of each
`F_s(x)` as a sum (`CollatzPosDens.firstPassageLaw_finite`) is not needed for the identity.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §6.2.
-/

@[expose] public section

namespace CollatzPosDens

open ENNReal

open Classical in
/-- The first-step decomposition of `F_s(x)`, in `ℝ≥0∞`, given that the first-passage law at the
smaller levels is at most `1`. -/
private lemma firstPassageLaw_ofReal_eq (s : ℕ)
    (hb : ∀ t : ℤ, t < s → ∀ y, firstPassageLaw t y ≤ 1) (x : ℤ × ℤ) :
    ENNReal.ofReal (firstPassageLaw s x) =
      (if x ∈ bkPoints ∧ (s : ℤ) < bkL x then ENNReal.ofReal (holdLaw x.1.toNat x.2) else 0) +
      ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
        ENNReal.ofReal (holdLaw h.1.1.toNat h.1.2) *
          ENNReal.ofReal (firstPassageLaw (s - bkL h) (x - h)) := by
  have hηs : Summable fun h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s} ↦
      holdLaw h.1.1.toNat h.1.2 := by
    have hg : Summable (Set.indicator bkPoints fun p : ℤ × ℤ ↦ holdLaw p.1.toNat p.2) :=
      summable_subtype_iff_indicator.1 hasSum_holdLaw_bkPoints.summable
    refine (hg.subtype {h : ℤ × ℤ | h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}).congr fun h ↦ ?_
    simp [Set.indicator_of_mem h.2.1]
  have hsum : Summable fun h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s} ↦
      holdLaw h.1.1.toNat h.1.2 * firstPassageLaw (s - bkL h) (x - h) := by
    refine hηs.of_nonneg_of_le
      (fun h ↦ mul_nonneg (holdLaw_nonneg _ _) (firstPassageLaw_nonneg _ _)) fun h ↦ ?_
    refine mul_le_of_le_one_right (holdLaw_nonneg _ _) (hb _ ?_ _)
    have := h.2.2.1
    omega
  have n1 : 0 ≤ if x ∈ bkPoints ∧ (s : ℤ) < bkL x then holdLaw x.1.toNat x.2 else 0 := by
    split_ifs
    · exact holdLaw_nonneg _ _
    · exact le_rfl
  have n2 : 0 ≤ ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
      holdLaw h.1.1.toNat h.1.2 * firstPassageLaw (s - bkL h) (x - h) :=
    tsum_nonneg fun h ↦ mul_nonneg (holdLaw_nonneg _ _) (firstPassageLaw_nonneg _ _)
  rw [firstPassageLaw_eq_first_step, firstPassageLaw_eq_first_step_tsum_ite,
    ENNReal.ofReal_add n1 n2,
    ENNReal.ofReal_tsum_of_nonneg
      (fun h ↦ mul_nonneg (holdLaw_nonneg _ _) (firstPassageLaw_nonneg _ _)) hsum]
  congr 1
  · split_ifs <;> simp
  · congr 1
    ext h
    exact ENNReal.ofReal_mul (holdLaw_nonneg _ _)

/-- The total mass of `F_s` is `1`, in `ℝ≥0∞`, given that the first-passage law at the smaller
levels is at most `1` and has total mass `1`. -/
private lemma tsum_firstPassageLaw_ofReal (s : ℕ)
    (hb : ∀ t : ℤ, t < s → ∀ y, firstPassageLaw t y ≤ 1)
    (ih : ∀ m < s, ∑' x, ENNReal.ofReal (firstPassageLaw m x) = 1) :
    ∑' x, ENNReal.ofReal (firstPassageLaw s x) = 1 := by
  classical
  simp only [firstPassageLaw_ofReal_eq s hb]
  rw [ENNReal.tsum_add, ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left]
  have hshift : ∀ h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
      ∑' x, ENNReal.ofReal (firstPassageLaw (s - bkL h) (x - h)) = 1 := by
    rintro ⟨h, hp, hl1, hl2⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = s - bkL h := ⟨(s - bkL h).toNat, by omega⟩
    have hms : m < s := by omega
    rw [← hm, ← ih m hms]
    exact (Equiv.subRight h).tsum_eq fun x ↦ ENNReal.ofReal (firstPassageLaw m x)
  simp only [hshift, mul_one]
  have hmass : ∑' p : bkPoints, ENNReal.ofReal (holdLaw p.1.1.toNat p.1.2) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ holdLaw_nonneg _ _)
      hasSum_holdLaw_bkPoints.summable, tsum_holdLaw_bkPoints, ENNReal.ofReal_one]
  rw [← hmass, tsum_bkPoints_eq_add s (G := fun p ↦ ENNReal.ofReal (holdLaw p.1.toNat p.2))
    fun h hη ↦ by simp [hη]]
  congr 1
  refine Eq.trans ?_ (tsum_subtype {h : ℤ × ℤ | h ∈ bkPoints ∧ (s : ℤ) < bkL h}
    fun p ↦ ENNReal.ofReal (holdLaw p.1.toNat p.2)).symm
  exact tsum_congr fun p ↦ by simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- A nonnegative real function with total mass `1` in `ℝ≥0∞` has sum `1`. -/
private lemma hasSum_firstPassageLaw_of_tsum_ofReal (s : ℕ)
    (h : ∑' x, ENNReal.ofReal (firstPassageLaw s x) = 1) :
    HasSum (fun x ↦ firstPassageLaw s x) 1 := by
  have hne : ∑' x, ENNReal.ofReal (firstPassageLaw s x) ≠ ∞ := by
    rw [h]; exact one_ne_top
  have hs : Summable fun x ↦ firstPassageLaw s x := by
    simpa [ENNReal.toReal_ofReal (firstPassageLaw_nonneg _ _)] using ENNReal.summable_toReal hne
  convert hs.hasSum
  rw [← ENNReal.toReal_ofReal (tsum_nonneg fun x ↦ firstPassageLaw_nonneg s x),
    ENNReal.ofReal_tsum_of_nonneg (fun x ↦ firstPassageLaw_nonneg s x) hs, h,
    ENNReal.toReal_one]

/-- The total mass of `F_s` is `1`, both in `ℝ≥0∞` and as a real `HasSum`. -/
private lemma firstPassageLaw_mass_aux (s : ℕ) :
    ∑' x, ENNReal.ofReal (firstPassageLaw s x) = 1 ∧ HasSum (fun x ↦ firstPassageLaw s x) 1 := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  have hb : ∀ t : ℤ, t < s → ∀ y, firstPassageLaw t y ≤ 1 := by
    intro t ht y
    rcases lt_or_ge t 0 with h0 | h0
    · rw [firstPassageLaw_of_neg h0]; exact zero_le_one
    · lift t to ℕ using h0
      exact le_hasSum (ih t (by exact_mod_cast ht)).2 y fun _ _ ↦ firstPassageLaw_nonneg _ _
  have h := tsum_firstPassageLaw_ofReal s hb fun m hm ↦ (ih m hm).1
  exact ⟨h, hasSum_firstPassageLaw_of_tsum_ofReal s h⟩

/-- **Total mass of the first-passage law.** For every `s ∈ ℕ`, `x ↦ F_s(x)` has sum `1`
(in particular the series converges). -/
@[collatz_pos_dens "lem_rn_fp_mass"]
theorem hasSum_firstPassageLaw (s : ℕ) : HasSum (fun x ↦ firstPassageLaw s x) 1 :=
  (firstPassageLaw_mass_aux s).2

/-- **Total mass of the first-passage law.** For every `s ∈ ℕ`,
`∑_{x ∈ ℤ × ℤ} F_s(x) = 1`. -/
@[collatz_pos_dens "lem_rn_fp_mass"]
theorem tsum_firstPassageLaw (s : ℕ) : ∑' x, firstPassageLaw s x = 1 :=
  (hasSum_firstPassageLaw s).tsum_eq

/-- The first-passage law is summable at every level `s ∈ ℕ`. -/
theorem summable_firstPassageLaw (s : ℕ) : Summable fun x ↦ firstPassageLaw s x :=
  (hasSum_firstPassageLaw s).summable

/-- The first-passage law takes values at most `1`, at every level. -/
theorem firstPassageLaw_le_one (s : ℤ) (x : ℤ × ℤ) : firstPassageLaw s x ≤ 1 := by
  rcases lt_or_ge s 0 with h0 | h0
  · rw [firstPassageLaw_of_neg h0]; exact zero_le_one
  · lift s to ℕ using h0
    exact le_hasSum (hasSum_firstPassageLaw s) x fun _ _ ↦ firstPassageLaw_nonneg _ _

open Classical in
/-- **First-step decomposition of `F_s(x)` in `ℝ≥0∞`.**
`F_s(x) = η(x) [x ∈ 𝒫, l(x) > s] + ∑_{h ∈ 𝒫, 1 ≤ l(h) ≤ s} η(h) F_{s - l(h)}(x - h)`. -/
theorem ofReal_firstPassageLaw_eq_first_step (s : ℕ) (x : ℤ × ℤ) :
    ENNReal.ofReal (firstPassageLaw s x) =
      (if x ∈ bkPoints ∧ (s : ℤ) < bkL x then ENNReal.ofReal (holdLaw x.1.toNat x.2) else 0) +
      ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
        ENNReal.ofReal (holdLaw h.1.1.toNat h.1.2) *
          ENNReal.ofReal (firstPassageLaw (s - bkL h) (x - h)) :=
  firstPassageLaw_ofReal_eq s (fun t _ y ↦ firstPassageLaw_le_one t y) x

/-- The first-passage law restricted to `ℕ × ℤ` is summable. -/
theorem summable_firstPassageLaw_natCast (s : ℕ) :
    Summable fun x : ℕ × ℤ ↦ firstPassageLaw s ((x.1 : ℤ), x.2) :=
  (summable_firstPassageLaw s).comp_injective natCast_prod_injective

/-- The first-passage law restricted to `ℕ × ℤ` has total mass at most `1`. -/
theorem tsum_firstPassageLaw_natCast_le_one (s : ℕ) :
    ∑' x : ℕ × ℤ, firstPassageLaw s ((x.1 : ℤ), x.2) ≤ 1 :=
  (tsum_comp_le_tsum_of_inj (summable_firstPassageLaw s) (firstPassageLaw_nonneg s)
    natCast_prod_injective).trans (tsum_firstPassageLaw s).le

/-- The restriction of `F_s` to `ℕ × ℤ` has total mass at most `1`, as a sum in `[0, ∞]`. -/
theorem tsum_ofReal_firstPassageLaw_natCast_le_one (s : ℕ) :
    ∑' x : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw s ((x.1 : ℤ), x.2)) ≤ 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ firstPassageLaw_nonneg _ _)
    (summable_firstPassageLaw_natCast s)]
  exact ENNReal.ofReal_le_one.2 (tsum_firstPassageLaw_natCast_le_one s)

end CollatzPosDens
