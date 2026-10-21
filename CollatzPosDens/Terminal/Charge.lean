/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.S06PairWeight
public import CollatzPosDens.Terminal.SourceUniqueHistory

/-!
# The source charge

Let `t ≥ t_min` (`CollatzPosDens.targetFloor`, equal to `16^{16544}`) be an odd integer that is
not Syracuse-periodic, let `j ≥ 0`, and let `X` be admissible for generation `j`. Then
`X Υ_{j,X}(t) ≤ t · #𝒮_{j,X}(t)`.

Every counted pair `(h, w)` of `Υ_{j,X}(t)` has `ω(h) ω(w) ≤ t / X`, and the source map
`(h, w) ↦ src(w, R_h)` is a bijection from the counted pairs onto `𝒮_{j,X}(t)`: it is
surjective by definition of the source set and injective because a counted pair is determined
by its source. Summing over the counted pairs gives `Υ_{j,X}(t) ≤ (t / X) · #𝒮_{j,X}(t)`.

## Main results

* `CollatzPosDens.ncard_sources_eq`: `#𝒮_{j,X}(t)` is the number of counted pairs.
* `CollatzPosDens.mul_unweightedMass_le_of_odd`: `X Υ_{j,X}(t) ≤ t · #𝒮_{j,X}(t)`.
* `CollatzPosDens.GoodSeed.mul_unweightedMass_le`: the same bound for an `s`-good seed with
  `s ≥ 1`, which is odd, not Syracuse-periodic and exceeds `2^{σ_sd} = t_min`.

## Implementation notes

The cardinality `#𝒮_{j,X}(t)` is `Set.ncard`; the source set is finite
(`CollatzPosDens.sources_finite`), so this is its genuine number of elements. The counting
identity `ncard_sources_eq` holds for every real `X` and needs only that `t` is a positive odd
integer that is not Syracuse-periodic.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- For a positive odd integer `t` that is not Syracuse-periodic, the source set `𝒮_{j,X}(t)`
has as many elements as there are counted pairs of `Υ_{j,X}(t)`. -/
theorem ncard_sources_eq {t : ℕ} (hpos : 0 < t) (hodd : Odd t) (hper : ¬ SyrPeriodic t)
    (j : ℕ) (X : ℝ) : (sources j X t).ncard = (unweightedMassPairs j X t).ncard := by
  rw [← Set.ncard_image_of_injective _ (Int.cast_injective (α := ℚ)), image_intCast_sources,
    Set.InjOn.ncard_image]
  rintro ⟨h, w⟩ hp ⟨h', w'⟩ hq hsrc
  exact eq_of_src_eq_of_mem_unweightedMassPairs hpos hodd hper hp hq hsrc

/-- **Source charge.** Let `t ≥ t_min` be an odd integer that is not Syracuse-periodic, let
`j ≥ 0`, and let `X` be admissible for generation `j`. Then `X Υ_{j,X}(t) ≤ t · #𝒮_{j,X}(t)`. -/
@[collatz_pos_dens "lem_charge"]
theorem mul_unweightedMass_le_of_odd {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t)
    (hper : ¬ SyrPeriodic t) {j : ℕ} {X : ℝ} (hX : IsAdmissibleScale t j X) :
    X * unweightedMass j X t ≤ t * (sources j X t).ncard := by
  have hfin := unweightedMassPairs_finite j X t
  have hX' : IsAdmissibleScale ((t : ℤ) : ℚ) j X := by rwa [Int.cast_natCast]
  have hsum : unweightedMass j X t ≤ (unweightedMassPairs j X t).ncard * ((t : ℝ) / X) := by
    rw [unweightedMass_eq_finsum_pairs, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Set.ncard_eq_toFinset_card _ hfin, ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    rw [Set.Finite.mem_toFinset] at hp
    have hp' : (p.1, p.2) ∈ unweightedMassPairs j X ((t : ℤ) : ℚ) := by
      rwa [Int.cast_natCast]
    have := weight_mul_weight_le_div_of_odd (t := (t : ℤ)) (by exact_mod_cast hodd)
      (by exact_mod_cast ht) hX' hp'
    simpa only [Int.cast_natCast] using this
  rw [ncard_sources_eq hodd.pos hodd hper]
  calc X * unweightedMass j X t
      ≤ X * ((unweightedMassPairs j X t).ncard * ((t : ℝ) / X)) :=
        mul_le_mul_of_nonneg_left hsum hX.1.le
    _ = t * (unweightedMassPairs j X t).ncard := by
        field_simp [hX.1.ne']

/-- **Source charge for a good seed.** Let `s ≥ 1`, let `M` be an `s`-good seed, and let `X` be
admissible for generation `n`. Then `X Υ_{n,X}(M) ≤ M · #𝒮_{n,X}(M)`. -/
theorem GoodSeed.mul_unweightedMass_le {s M n : ℕ} {X : ℝ} (hM : GoodSeed s M) (hs : 0 < s)
    (hX : IsAdmissibleScale M n X) :
    X * unweightedMass n X M ≤ M * (sources n X M).ncard := by
  have hfl : targetFloor ≤ M := by
    have h := (hM.two_pow_66176_lt hs).le
    rwa [show (66176 : ℕ) = 4 * 16544 by norm_num, pow_mul, show (2 : ℕ) ^ 4 = 16 by norm_num,
      ← targetFloor_eq] at h
  exact mul_unweightedMass_le_of_odd hM.odd hfl hM.not_syrPeriodic hX

end CollatzPosDens
