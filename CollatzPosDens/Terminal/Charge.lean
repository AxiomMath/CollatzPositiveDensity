/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.Sources
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.PairWeight
public import CollatzPosDens.Terminal.SourceUniqueHistory

/-!
# The source charge

Let `M` be a good seed, `n ≥ 0`, and let `X` be admissible for generation `n`. Then
`X Υ_{n,X}(M) ≤ M · #𝒮_{n,X}(M)`.

Every counted pair `(h, w)` of `Υ_{n,X}(M)` has `ω(h) ω(w) ≤ M / X`, and the source map
`(h, w) ↦ src(w, R_h)` is a bijection from the counted pairs onto `𝒮_{n,X}(M)`: it is
surjective by definition of the source set and injective because a counted pair is determined
by its source. Summing over the counted pairs gives `Υ_{n,X}(M) ≤ (M / X) · #𝒮_{n,X}(M)`.

## Main results

* `CollatzPosDens.GoodSeed.ncard_sources_eq`: `#𝒮_{n,X}(M)` is the number of counted pairs.
* `CollatzPosDens.GoodSeed.mul_unweightedMass_le`: `X Υ_{n,X}(M) ≤ M · #𝒮_{n,X}(M)`.

## Implementation notes

The cardinality `#𝒮_{n,X}(M)` is `Set.ncard`; the source set is finite
(`CollatzPosDens.sources_finite`), so this is its genuine number of elements. The counting
identity `GoodSeed.ncard_sources_eq` holds for every real `X`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {M : ℕ} {n : ℕ} {X : ℝ}

/-- For a good seed `M`, the source set `𝒮_{n,X}(M)` has as many elements as there are
counted pairs of `Υ_{n,X}(M)`. -/
theorem GoodSeed.ncard_sources_eq (hM : GoodSeed M) (n : ℕ) (X : ℝ) :
    (sources n X M).ncard = (unweightedMassPairs n X M).ncard := by
  rw [← Set.ncard_image_of_injective _ (Int.cast_injective (α := ℚ)), image_intCast_sources,
    Set.InjOn.ncard_image]
  rintro ⟨h, w⟩ hp ⟨h', w'⟩ hq hs
  exact eq_of_src_eq_of_mem_unweightedMassPairs hM hp hq hs

/-- **Source charge.** Let `M` be a good seed and let `X` be admissible for generation `n`.
Then `X Υ_{n,X}(M) ≤ M · #𝒮_{n,X}(M)`. -/
@[collatz_pos_dens "lem_charge"]
theorem GoodSeed.mul_unweightedMass_le (hM : GoodSeed M) (hX : IsAdmissibleScale M n X) :
    X * unweightedMass n X M ≤ M * (sources n X M).ncard := by
  have hfin := unweightedMassPairs_finite n X M
  have hsum : unweightedMass n X M ≤ (unweightedMassPairs n X M).ncard * ((M : ℝ) / X) := by
    rw [unweightedMass_eq_finsum_pairs, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Set.ncard_eq_toFinset_card _ hfin, ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    rw [Set.Finite.mem_toFinset] at hp
    exact hM.weight_mul_weight_le_div hX hp
  rw [hM.ncard_sources_eq]
  calc X * unweightedMass n X M
      ≤ X * ((unweightedMassPairs n X M).ncard * ((M : ℝ) / X)) :=
        mul_le_mul_of_nonneg_left hsum hX.pos.le
    _ = M * (unweightedMassPairs n X M).ncard := by
        field_simp [hX.pos.ne']

end CollatzPosDens
