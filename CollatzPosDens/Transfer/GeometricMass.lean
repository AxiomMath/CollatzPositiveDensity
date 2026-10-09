/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum

/-!
# Geometric mass of a set of words

For a set `𝒱` of words, its *geometric mass* is
`𝐩(𝒱) = ∑_{w ∈ 𝒱} 2^{-A(w)} ∈ [0, ∞]`, where `A(w)` is the valuation sum of `w`.

## Main definitions

* `CollatzPosDens.geomMass`: the geometric mass `𝐩(𝒱)` of a set of words.

## Main results

* `CollatzPosDens.geomMass_mono`: `𝐩` is monotone in the set.
* `CollatzPosDens.geomMass_union_le`: `𝐩` is subadditive.
* `CollatzPosDens.geomMass_union`: `𝐩` is additive on disjoint sets.
* `CollatzPosDens.geomMass_singleton`: `𝐩({w}) = 2^{-A(w)}`.
* `CollatzPosDens.toReal_geomMass_coe_finset`: for finite `s`, `𝐩(s) = ∑_{w ∈ s} 2^{-A(w)}` in `ℝ`.

## Implementation notes

The weight `2^{-A(w)}` is written `2⁻¹ ^ A(w)` in `ℝ≥0∞`, so that the sum is an unconditional
`tsum` of nonnegative terms, always defined and possibly `∞`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The geometric-mass weight `2^{-A(w)}` of a word `w`, in `ℝ≥0∞`. This is distinct from
`CollatzPosDens.Word.weight`. -/
noncomputable abbrev Word.massWeight (w : Word) : ℝ≥0∞ := 2⁻¹ ^ w.valSum

/-- The geometric mass `𝐩(𝒱) = ∑_{w ∈ 𝒱} 2^{-A(w)} ∈ [0, ∞]` of a set `𝒱` of words. -/
@[collatz_pos_dens "def_geometric_mass"]
noncomputable def geomMass (V : Set Word) : ℝ≥0∞ := ∑' w : V, (w : Word).massWeight

/-- Unfolding lemma for `geomMass`. -/
theorem geomMass_def (V : Set Word) : geomMass V = ∑' w : V, (w : Word).massWeight := rfl

/-- The geometric mass as an indicator sum over all words. -/
theorem geomMass_eq_tsum_indicator (V : Set Word) :
    geomMass V = ∑' w : Word, V.indicator Word.massWeight w :=
  tsum_subtype V Word.massWeight

/-- The empty set has geometric mass `0`. -/
@[simp]
theorem geomMass_empty : geomMass ∅ = 0 := by
  simp [geomMass]

/-- A single word has geometric mass `2^{-A(w)}`. -/
@[simp]
theorem geomMass_singleton (w : Word) : geomMass {w} = 2⁻¹ ^ w.valSum := by
  simp [geomMass]

/-- The geometric mass is monotone. -/
theorem geomMass_mono {U V : Set Word} (h : U ⊆ V) : geomMass U ≤ geomMass V :=
  ENNReal.tsum_mono_subtype _ h

/-- The geometric mass is subadditive. -/
theorem geomMass_union_le (U V : Set Word) : geomMass (U ∪ V) ≤ geomMass U + geomMass V :=
  ENNReal.tsum_union_le _ U V

/-- The geometric mass is additive on disjoint sets. -/
theorem geomMass_union {U V : Set Word} (h : Disjoint U V) :
    geomMass (U ∪ V) = geomMass U + geomMass V :=
  ENNReal.summable.tsum_union_disjoint h ENNReal.summable

/-- The geometric mass of a finite set is the finite sum of the weights. -/
theorem geomMass_coe_finset (s : Finset Word) :
    geomMass (s : Set Word) = ∑ w ∈ s, 2⁻¹ ^ w.valSum :=
  Finset.tsum_subtype s Word.massWeight

/-- The geometric mass of a finite set is finite. -/
theorem geomMass_coe_finset_ne_top (s : Finset Word) : geomMass (s : Set Word) ≠ ⊤ := by
  rw [geomMass_coe_finset]
  exact ENNReal.sum_ne_top.2 fun w _ => ENNReal.pow_ne_top (by simp)

/-- The geometric mass of a finite set, as a real number, is the finite sum of the weights. -/
theorem toReal_geomMass_coe_finset (s : Finset Word) :
    (geomMass (s : Set Word)).toReal = ∑ w ∈ s, (2 : ℝ)⁻¹ ^ w.valSum := by
  rw [geomMass_coe_finset, ENNReal.toReal_sum fun w _ => ENNReal.pow_ne_top (by simp)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

end CollatzPosDens
