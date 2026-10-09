/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.ResidueMap

/-!
# Submass of a set of words

For `n ∈ ℕ`, a set `𝒱` of words and a residue `y ∈ G_n = ℤ/3^nℤ`, the *submass* of `𝒱` at `y`
is the part of the geometric mass of `𝒱` carried by the words whose offset reduces to `y`:
$$\mathrm{Sub}^n_{\mathcal V}(y) = \sum_{w \in \mathcal V,\ [\mathrm{off}(w)]_n = y} 2^{-A(w)}
  \in [0, \infty].$$

## Main definitions

* `CollatzPosDens.subMass`: the submass `Sub^n_𝒱(y)`.

## Main results

* `CollatzPosDens.subMass_def`: `Sub^n_𝒱(y)` is the geometric mass of the fibre
  `{w ∈ 𝒱 | [off(w)]_n = y}`.
* `CollatzPosDens.subMass_eq_tsum`: the defining series over `𝒱` with an indicator of the fibre.
* `CollatzPosDens.subMass_mono`: `Sub^n_𝒱(y)` is monotone in `𝒱`.
* `CollatzPosDens.subMass_le_geomMass`: `Sub^n_𝒱(y) ≤ 𝐩(𝒱)`.

## Implementation notes

The submass is usually considered for `𝒱 ⊆ ℤ_{≥1}^n`, i.e. a set of words of length `n`.
`subMass` accepts any set of words; the length restriction is a hypothesis of the lemmas that
use it. The reduction `[off(w)]_n` is `dyadicRed n` applied to the offset, which is a dyadic
rational.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.1.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The submass `Sub^n_𝒱(y) = ∑_{w ∈ 𝒱, [off(w)]_n = y} 2^{-A(w)} ∈ [0, ∞]`: the geometric
mass of the words of `𝒱` whose offset reduces to `y` modulo `3^n`. -/
@[collatz_pos_dens "def_mx_submass"]
noncomputable def subMass (n : ℕ) (V : Set Word) (y : ResidueGroup n) : ℝ≥0∞ :=
  geomMass {w | w ∈ V ∧ dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ = y}

/-- Unfolding lemma for `subMass`. -/
theorem subMass_def (n : ℕ) (V : Set Word) (y : ResidueGroup n) :
    subMass n V y =
      geomMass {w | w ∈ V ∧ dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ = y} :=
  rfl

/-- The submass as the series over `𝒱` of `2^{-A(w)}` restricted to `[off(w)]_n = y`. -/
theorem subMass_eq_tsum (n : ℕ) (V : Set Word) (y : ResidueGroup n) :
    subMass n V y = ∑' w : V,
      if dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ = y then (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum
      else 0 := by
  rw [subMass_def, geomMass_eq_tsum_indicator, tsum_subtype V (fun w : Word =>
    if dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ = y then (2⁻¹ : ℝ≥0∞) ^ w.valSum else 0)]
  refine tsum_congr fun w => ?_
  by_cases hV : w ∈ V <;> by_cases h : dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ = y <;>
    simp [Set.indicator, h, hV]

/-- The submass is monotone in the set of words. -/
theorem subMass_mono (n : ℕ) {U V : Set Word} (h : U ⊆ V) (y : ResidueGroup n) :
    subMass n U y ≤ subMass n V y :=
  geomMass_mono fun _ hw => ⟨h hw.1, hw.2⟩

/-- The submass is at most the geometric mass: `Sub^n_𝒱(y) ≤ 𝐩(𝒱)`. -/
theorem subMass_le_geomMass (n : ℕ) (V : Set Word) (y : ResidueGroup n) :
    subMass n V y ≤ geomMass V :=
  geomMass_mono fun _ hw => hw.1

end CollatzPosDens
