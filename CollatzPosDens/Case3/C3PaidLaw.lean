/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3PaidPassage
public import CollatzPosDens.StoppingTrace.TrAtoms
public import CollatzPosDens.StoppingTrace.TrListWeight
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The paid fresh law

Fix a level `n` and a residue `ξ ∈ G_n`, and let the paid passage mass `F̃_e` refer to
`(n, ξ, ε_*)`. For a black point `e ∈ 𝒫`, the *paid fresh law* is the weight
`μ̃_e(a) = F̃_e(r, ℓ) · bw^⊗(β)` on the fresh atoms `a = ((r, ℓ), β) ∈ 𝒜_n`: a paid passage above
the gap of `e` landing at the displacement `(r, ℓ)`, followed by the `⌊n/2⌋` blocks of `β`,
weighted independently by the block weight. For a set `ℰ` of atoms,
`μ̃_e(ℰ) = ∑_{a ∈ ℰ} μ̃_e(a)`.

## Main definitions

* `CollatzPosDens.c3PaidLaw`: the paid fresh law `μ̃_e(a)` of an atom.
* `CollatzPosDens.c3PaidLawMass`: the paid fresh law `μ̃_e(ℰ)` of a set of atoms.

## Main results

* `CollatzPosDens.c3PaidLaw_mk`: `μ̃_e((r, ℓ), β) = F̃_e(r, ℓ) · bw^⊗(β)`.
* `CollatzPosDens.c3PaidLaw_zero_left`: `μ̃_e((0, ℓ), β) = 0`, since a paid passage moves the
  first coordinate by at least `1`.
* `CollatzPosDens.c3PaidLawMass_mono`, `CollatzPosDens.c3PaidLawMass_union_le`,
  `CollatzPosDens.c3PaidLawMass_union`: `μ̃_e` is monotone, subadditive, and additive on
  disjoint sets of atoms.

## Implementation notes

The paid passage mass `F̃_e(x)` is an `ℝ≥0∞`-valued sum, so the paid fresh law is valued in
`[0, ∞]` too, with the real weight `bw^⊗(β) ≥ 0` embedded through `ENNReal.ofReal`; the mass of a
set of atoms is then an unconditional `tsum` over the subtype. As for the fresh law `trFreshLaw`,
the law is defined by the same formula on all of `(ℕ × ℤ) × List (List ℤ × ℤ)`; its restriction
to `𝒜_n = trAtoms n` is `μ̃_e`, and the mass of a set of fresh atoms is the mass of the
corresponding subset of the ambient type. The displacement `r ∈ ℕ` is read in `ℤ` for `F̃_e`.
Blackness of `e` and `e ∈ 𝒫` play no role in the definition and are not assumed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- The paid fresh law `μ̃_e(a) = F̃_e(r, ℓ) · bw^⊗(β)` of an atom `a = ((r, ℓ), β)`, where
`F̃_e` is the paid passage mass for `(n, ξ, ε_*)` (defined by the same formula on all of
`(ℕ × ℤ) × List (List ℤ × ℤ)`). -/
@[collatz_pos_dens "def_c3_paid_law"]
noncomputable def c3PaidLaw (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ)
    (a : (ℕ × ℤ) × List (List ℤ × ℤ)) : ℝ≥0∞ :=
  c3PaidPassage n ξ e ((a.1.1 : ℤ), a.1.2) * ENNReal.ofReal (trListWeight a.2)

/-- The paid fresh law `μ̃_e(ℰ) = ∑_{a ∈ ℰ} μ̃_e(a)` of a set `ℰ` of atoms. -/
@[collatz_pos_dens "def_c3_paid_law"]
noncomputable def c3PaidLawMass (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ)
    (E : Set ((ℕ × ℤ) × List (List ℤ × ℤ))) : ℝ≥0∞ :=
  ∑' a : E, c3PaidLaw n ξ e a

variable {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ}

/-- The paid fresh law of an atom is the paid passage mass at its displacement times the block
weight of its block list. -/
lemma c3PaidLaw_def (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    c3PaidLaw n ξ e a =
      c3PaidPassage n ξ e ((a.1.1 : ℤ), a.1.2) * ENNReal.ofReal (trListWeight a.2) :=
  rfl

/-- The paid fresh law at an atom written `((r, ℓ), β)`. -/
@[simp]
lemma c3PaidLaw_mk (r : ℕ) (ℓ : ℤ) (β : List (List ℤ × ℤ)) :
    c3PaidLaw n ξ e ((r, ℓ), β) =
      c3PaidPassage n ξ e ((r : ℤ), ℓ) * ENNReal.ofReal (trListWeight β) :=
  rfl

/-- The paid fresh law with an empty block list is the paid passage mass. -/
lemma c3PaidLaw_nil (r : ℕ) (ℓ : ℤ) :
    c3PaidLaw n ξ e ((r, ℓ), []) = c3PaidPassage n ξ e ((r : ℤ), ℓ) := by
  simp

/-- The paid passage mass vanishes at a displacement with first coordinate below `1`. -/
lemma c3PaidPassage_eq_zero_of_fst_lt_one {x : ℤ × ℤ} (hx : x.1 < 1) :
    c3PaidPassage n ξ e x = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun π => ite_eq_right_iff.mpr fun h => absurd ?_ hx.not_ge
  rw [← h]
  exact one_le_chBlockPath_length_fst (ne_nil_of_mem_trPassage π.2)

/-- `μ̃_e((0, ℓ), β) = 0`: a paid passage moves the first coordinate by at least `1`. -/
@[simp]
lemma c3PaidLaw_zero_left (ℓ : ℤ) (β : List (List ℤ × ℤ)) :
    c3PaidLaw n ξ e ((0, ℓ), β) = 0 := by
  rw [c3PaidLaw_mk, c3PaidPassage_eq_zero_of_fst_lt_one (by simp), zero_mul]

/-- The paid fresh law of a set of atoms is the sum of the laws of its atoms. -/
lemma c3PaidLawMass_def (E : Set ((ℕ × ℤ) × List (List ℤ × ℤ))) :
    c3PaidLawMass n ξ e E = ∑' a : E, c3PaidLaw n ξ e a :=
  rfl

/-- The paid fresh law of a set as an indicator sum over all atoms. -/
lemma c3PaidLawMass_eq_tsum_indicator (E : Set ((ℕ × ℤ) × List (List ℤ × ℤ))) :
    c3PaidLawMass n ξ e E = ∑' a, E.indicator (c3PaidLaw n ξ e) a :=
  tsum_subtype E _

/-- The empty set of atoms has paid fresh law `0`. -/
@[simp]
lemma c3PaidLawMass_empty : c3PaidLawMass n ξ e ∅ = 0 := by
  simp [c3PaidLawMass]

/-- The paid fresh law of a single atom. -/
@[simp]
lemma c3PaidLawMass_singleton (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    c3PaidLawMass n ξ e {a} = c3PaidLaw n ξ e a := by
  simp [c3PaidLawMass]

/-- The paid fresh law of a finite set of atoms is a finite sum. -/
lemma c3PaidLawMass_coe_finset (s : Finset ((ℕ × ℤ) × List (List ℤ × ℤ))) :
    c3PaidLawMass n ξ e s = ∑ a ∈ s, c3PaidLaw n ξ e a := by
  exact Finset.tsum_subtype s (c3PaidLaw n ξ e)

/-- The paid fresh law is monotone in the set of atoms. -/
lemma c3PaidLawMass_mono {E F : Set ((ℕ × ℤ) × List (List ℤ × ℤ))} (h : E ⊆ F) :
    c3PaidLawMass n ξ e E ≤ c3PaidLawMass n ξ e F :=
  ENNReal.tsum_mono_subtype _ h

/-- The paid fresh law is subadditive. -/
lemma c3PaidLawMass_union_le (E F : Set ((ℕ × ℤ) × List (List ℤ × ℤ))) :
    c3PaidLawMass n ξ e (E ∪ F) ≤ c3PaidLawMass n ξ e E + c3PaidLawMass n ξ e F :=
  ENNReal.tsum_union_le _ E F

/-- The paid fresh law is additive on disjoint sets of atoms. -/
lemma c3PaidLawMass_union {E F : Set ((ℕ × ℤ) × List (List ℤ × ℤ))} (h : Disjoint E F) :
    c3PaidLawMass n ξ e (E ∪ F) = c3PaidLawMass n ξ e E + c3PaidLawMass n ξ e F :=
  Summable.tsum_union_disjoint h ENNReal.summable ENNReal.summable

end CollatzPosDens
