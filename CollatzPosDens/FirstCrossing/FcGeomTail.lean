/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal

/-!
# Geometric tails are binomial tails

Under the geometric mass `𝐩`, the letters of a word of length `h` behave like `h` independent
geometric variables of parameter `1/2`. The tail of their sum is a binomial tail:
for `h ≥ 0` and `s ≥ 1`,
`𝐩({x ∈ ℤ_{≥1}^h : A(x) ≥ s}) = 2^{-(s-1)} ∑_{t=0}^{h-1} (s-1 choose t)`,
the probability that `s - 1` fair coin flips show fewer than `h` heads.

## Main results

* `CollatzPosDens.geomMass_setOf_length_eq_le_valSum`: the identity above.
* `CollatzPosDens.geomMass_setOf_length_eq_le_valSum_succ_succ`: the recursion
  `F(h+1, s+1) = F(h, s)/2 + F(h+1, s)/2` for `F(h, s) = 𝐩({x ∈ ℤ_{≥1}^h : A(x) ≥ s})`.

## Implementation notes

Words of length `h` stand for `ℤ_{≥1}^h`. Rather than summing compositions and telescoping, we
split a word by its first letter: either it is `1`, which leaves a word of length `h` with tail
sum at least `s`, or it is `b + 1`, and lowering it to `b` leaves a word of length `h + 1` with
sum at least `s`. Each branch carries a factor `1/2`, which gives the recursion above; the
binomial side satisfies the same recursion by Pascal's rule. The identity holds for `h = 0` as
well (both sides vanish), so no hypothesis `h ≥ 1` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The geometric mass of `{x : |x| = h, A(x) ≥ 0}` is `1`. -/
theorem geomMass_setOf_length_eq_le_valSum_zero (h : ℕ) :
    geomMass {x : Word | x.length = h ∧ 0 ≤ x.valSum} = 1 := by
  simpa using geomMass_setOf_length_eq h

/-- The geometric mass of `{x : |x| = 0, A(x) ≥ s + 1}` is `0`. -/
theorem geomMass_setOf_length_eq_le_valSum_zero_succ (s : ℕ) :
    geomMass {x : Word | x.length = 0 ∧ s + 1 ≤ x.valSum} = 0 := by
  have : {x : Word | x.length = 0 ∧ s + 1 ≤ x.valSum} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
      List.length_eq_zero_iff]
    rintro rfl
    simp
  rw [this, geomMass_empty]

private theorem geomMass_image_scale {g : Word → Word} (hg : Function.Injective g)
    {S : Set Word} (hw : ∀ x ∈ S, (g x).valSum = x.valSum + 1) :
    geomMass (g '' S) = 2⁻¹ * geomMass S := by
  rw [geomMass_def, tsum_image _ hg.injOn, geomMass_def, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  simp [Word.massWeight, hw x x.2, pow_succ, mul_comm]

/-- Splitting a word by its first letter: a word of length `h + 1` with sum at least `s + 1`
either starts with `1` followed by a word of length `h` with sum at least `s`, or is the
`incrHead` of a word of length `h + 1` with sum at least `s`. -/
theorem setOf_length_succ_le_valSum_succ_eq_union (h s : ℕ) :
    {x : Word | x.length = h + 1 ∧ s + 1 ≤ x.valSum} =
      List.cons 1 '' {x : Word | x.length = h ∧ s ≤ x.valSum} ∪
        Word.incrHead '' {x : Word | x.length = h + 1 ∧ s ≤ x.valSum} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨hl, hs⟩
    rcases x with _ | ⟨a, y⟩
    · simp at hl
    simp only [List.length_cons, Nat.add_right_cancel_iff, Word.valSum_cons] at hl hs
    rcases eq_or_ne a 1 with rfl | ha
    · refine Or.inl ⟨y, ⟨hl, ?_⟩, rfl⟩
      simp only [PNat.one_coe] at hs
      omega
    · right
      obtain ⟨b, rfl⟩ := PNat.exists_eq_succ_of_ne_one ha
      refine ⟨b :: y, ⟨by simp [hl], ?_⟩, rfl⟩
      simp only [Word.valSum_cons, PNat.add_coe, PNat.one_coe] at hs ⊢
      omega
  · rintro (⟨y, ⟨hl, hs⟩, rfl⟩ | ⟨y, ⟨hl, hs⟩, rfl⟩)
    · refine ⟨by simp [hl], ?_⟩
      simp only [Word.valSum_cons, PNat.one_coe]
      omega
    · cases y with
      | nil => simp at hl
      | cons b z =>
        simp only [Word.incrHead, List.length_cons] at hl ⊢
        refine ⟨hl, ?_⟩
        simp only [Word.valSum_cons, PNat.add_coe, PNat.one_coe] at hs ⊢
        omega

/-- First-letter recursion: with `F(h, s) = 𝐩({x : |x| = h, A(x) ≥ s})`,
`F(h+1, s+1) = F(h, s)/2 + F(h+1, s)/2`. -/
theorem geomMass_setOf_length_eq_le_valSum_succ_succ (h s : ℕ) :
    geomMass {x : Word | x.length = h + 1 ∧ s + 1 ≤ x.valSum} =
      2⁻¹ * geomMass {x : Word | x.length = h ∧ s ≤ x.valSum} +
        2⁻¹ * geomMass {x : Word | x.length = h + 1 ∧ s ≤ x.valSum} := by
  have hdisj : Disjoint (List.cons 1 '' {x : Word | x.length = h ∧ s ≤ x.valSum})
      (Word.incrHead '' {x : Word | x.length = h + 1 ∧ s ≤ x.valSum}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, -, rfl⟩ ⟨z, -, hz⟩
    cases z with
    | nil => simp [Word.incrHead] at hz
    | cons b w =>
      simp only [Word.incrHead, List.cons.injEq] at hz
      simpa using congrArg ((↑) : ℕ+ → ℕ) hz.1
  rw [setOf_length_succ_le_valSum_succ_eq_union, geomMass_union hdisj,
    geomMass_image_scale List.cons_injective (fun x _ => by simp [add_comm]),
    geomMass_image_scale Word.incrHead_injective]
  rintro x ⟨hl, -⟩
  cases x with
  | nil => simp at hl
  | cons a y =>
    simp only [Word.incrHead, Word.valSum_cons, PNat.add_coe, PNat.one_coe]
    omega

private theorem choose_sum_succ (h m : ℕ) :
    ∑ t ∈ Finset.range (h + 1), (m + 1).choose t =
      ∑ t ∈ Finset.range (h + 1), m.choose t + ∑ t ∈ Finset.range h, m.choose t := by
  rw [Finset.sum_range_succ' (m + 1).choose, Finset.sum_range_succ' m.choose]
  simp only [Nat.choose_succ_succ', Finset.sum_add_distrib, Nat.choose_zero_right]
  ring

/-- **Geometric tails are binomial tails.** For `h ≥ 0` and `s ≥ 1`,
`𝐩({x ∈ ℤ_{≥1}^h : A(x) ≥ s}) = 2^{-(s-1)} ∑_{t=0}^{h-1} (s-1 choose t)`. -/
@[collatz_pos_dens "lem_fc_geom_tail"]
theorem geomMass_setOf_length_eq_le_valSum (h s : ℕ) (hs : 1 ≤ s) :
    geomMass {x : Word | x.length = h ∧ s ≤ x.valSum} =
      2⁻¹ ^ (s - 1) * ∑ t ∈ Finset.range h, ((s - 1).choose t : ℝ≥0∞) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction m generalizing h with
  | zero =>
    cases h with
    | zero => simpa using geomMass_setOf_length_eq_le_valSum_zero_succ 0
    | succ h =>
      rw [geomMass_setOf_length_eq_le_valSum_succ_succ, geomMass_setOf_length_eq_le_valSum_zero,
        geomMass_setOf_length_eq_le_valSum_zero, ← mul_add, one_add_one_eq_two,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
      simp [Finset.sum_range_succ', Nat.choose_zero_succ]
  | succ m ih =>
    cases h with
    | zero => simpa using geomMass_setOf_length_eq_le_valSum_zero_succ (m + 1)
    | succ h =>
      rw [geomMass_setOf_length_eq_le_valSum_succ_succ, ih h (by omega), ih (h + 1) (by omega)]
      have := congrArg ((↑) : ℕ → ℝ≥0∞) (choose_sum_succ h m)
      push_cast at this
      rw [this, pow_succ]
      ring

end CollatzPosDens
