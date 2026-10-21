/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Finite.Lattice
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.LengthOk
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Terminal.TerminalShift

/-!
# The unweighted terminal mass `Υ_{j,X}(t)`

For `j : ℕ`, a real `X` and a starting point `t : ℚ`, the unweighted terminal mass is the double
sum
$$\Upsilon_{j,X}(t) = \sum_{h \in \mathcal H_j(t)} \omega(h) \sum_{w} \omega(w),$$
where `h` runs over the central histories `centralHistories t j`, and for each `h` the inner sum
runs over the words `w ∈ firstCrossing (scale j) u_h 1` satisfying `LengthOk (scale j) u_h w` and
`Admissible (historyEndpoint t h) w`. Here `u_h = historyShift j X t h` is the terminal shift of
`h`, and `ω(h)` is the weight of the concatenated word `concatWord h`. The pairs `(h, w)` occurring
in this double sum are the *counted pairs* of `Υ_{j,X}(t)`. Both sums are finite, by
`centralHistories_finite` and `firstCrossing_finite`.

## Main definitions

* `CollatzPosDens.unweightedMassWords j X t h`: the words `w` of the inner sum attached to `h`.
* `CollatzPosDens.unweightedMassPairs j X t`: the set of counted pairs `(h, w)`.
* `CollatzPosDens.unweightedMass j X t`: the unweighted terminal mass `Υ_{j,X}(t)`.

## Main results

* `CollatzPosDens.mem_unweightedMassWords`, `CollatzPosDens.mem_unweightedMassPairs`:
  the defining conditions of the index sets.
* `CollatzPosDens.unweightedMassWords_finite`, `CollatzPosDens.unweightedMassPairs_finite`:
  the index sets are finite.
* `CollatzPosDens.unweightedMass_eq_sum`: `Υ_{j,X}(t)` as an iterated `Finset` sum.
* `CollatzPosDens.unweightedMass_eq_finsum_pairs`: `Υ_{j,X}(t)` as the sum of `ω(h) ω(w)`
  over the counted pairs.
* `CollatzPosDens.unweightedMass_nonneg`: `0 ≤ Υ_{j,X}(t)`.

## Implementation notes

The sums are `finsum`s over sets, genuine finite sums by the finiteness lemmas above; the set of
counted pairs is a `Set` with a finiteness lemma, so `(unweightedMassPairs_finite j X t).toFinset`
is the corresponding `Finset`. The mass is real-valued; the weights `ω` are rational and are cast
to `ℝ`. The terminal shift `u_h` is a natural number, cast to `ℤ` to index the first-crossing
family. As for `𝓗_j(t)`, the starting point `t` is taken in `ℚ`, and neither its oddness and
positivity nor the positivity of `X` is needed to state the definition.

## References

* [Mazur, *Collatz positive density*], §17.1.
-/

@[expose] public section

namespace CollatzPosDens

variable {j : ℕ}

/-- The words of the inner sum of `Υ_{j,X}(t)` attached to a history `h`: the words
`w ∈ 𝒲(b_j, u_h, 1)` with `Λ_{b_j,u_h}(w)` that are admissible from the endpoint `R_h`. -/
def unweightedMassWords (j : ℕ) (X : ℝ) (t : ℚ) (h : Fin j → Word) : Set Word :=
  {w | w ∈ firstCrossing (scale j) (historyShift j X t h) 1 ∧
    LengthOk (scale j) (historyShift j X t h) w ∧ Admissible (historyEndpoint t h) w}

/-- The *counted pairs* of `Υ_{j,X}(t)`: the pairs `(h, w)` with `h ∈ 𝓗_j(t)`,
`w ∈ 𝒲(b_j, u_h, 1)`, `Λ_{b_j,u_h}(w)` and `w` admissible from `R_h`. -/
@[collatz_pos_dens "def_unweighted_mass"]
def unweightedMassPairs (j : ℕ) (X : ℝ) (t : ℚ) : Set ((Fin j → Word) × Word) :=
  {p | p.1 ∈ centralHistories t j ∧ p.2 ∈ unweightedMassWords j X t p.1}

/-- The unweighted terminal mass
`Υ_{j,X}(t) = ∑_{h ∈ 𝓗_j(t)} ω(h) ∑_w ω(w)`, the inner sum over `w ∈ 𝒲(b_j, u_h, 1)` with
`Λ_{b_j,u_h}(w)` and `w` admissible from `R_h`. -/
@[collatz_pos_dens "def_unweighted_mass"]
noncomputable def unweightedMass (j : ℕ) (X : ℝ) (t : ℚ) : ℝ :=
  ∑ᶠ h ∈ centralHistories t j,
    ((concatWord h).weight : ℝ) * ∑ᶠ w ∈ unweightedMassWords j X t h, (w.weight : ℝ)

/-- Membership in the inner index set of `Υ_{j,X}(t)`. -/
theorem mem_unweightedMassWords {X : ℝ} {t : ℚ} {h : Fin j → Word} {w : Word} :
    w ∈ unweightedMassWords j X t h ↔
      w ∈ firstCrossing (scale j) (historyShift j X t h) 1 ∧
        LengthOk (scale j) (historyShift j X t h) w ∧ Admissible (historyEndpoint t h) w :=
  Iff.rfl

/-- The defining condition of a counted pair of `Υ_{j,X}(t)`. -/
theorem mem_unweightedMassPairs {X : ℝ} {t : ℚ} {h : Fin j → Word} {w : Word} :
    (h, w) ∈ unweightedMassPairs j X t ↔
      h ∈ centralHistories t j ∧ w ∈ firstCrossing (scale j) (historyShift j X t h) 1 ∧
        LengthOk (scale j) (historyShift j X t h) w ∧ Admissible (historyEndpoint t h) w :=
  Iff.rfl

/-- The inner index set of `Υ_{j,X}(t)` is finite. -/
theorem unweightedMassWords_finite (j : ℕ) (X : ℝ) (t : ℚ) (h : Fin j → Word) :
    (unweightedMassWords j X t h).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

/-- The set of counted pairs of `Υ_{j,X}(t)` is finite. -/
theorem unweightedMassPairs_finite (j : ℕ) (X : ℝ) (t : ℚ) :
    (unweightedMassPairs j X t).Finite :=
  ((centralHistories_finite t j).biUnion fun h _ =>
    (unweightedMassWords_finite j X t h).image (Prod.mk h)).subset
    fun p hp => Set.mem_biUnion hp.1 ⟨p.2, hp.2, rfl⟩

/-- `Υ_{j,X}(t)` as an iterated `Finset` sum. -/
theorem unweightedMass_eq_sum (j : ℕ) (X : ℝ) (t : ℚ) :
    unweightedMass j X t = ∑ h ∈ (centralHistories_finite t j).toFinset,
      ((concatWord h).weight : ℝ) *
        ∑ w ∈ (unweightedMassWords_finite j X t h).toFinset, (w.weight : ℝ) := by
  rw [unweightedMass,
    finsum_mem_eq_finite_toFinset_sum _ (centralHistories_finite t j)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassWords_finite j X t h)]

/-- `Υ_{j,X}(t)` is the sum of `ω(h) ω(w)` over its counted pairs `(h, w)`. -/
theorem unweightedMass_eq_finsum_pairs (j : ℕ) (X : ℝ) (t : ℚ) :
    unweightedMass j X t =
      ∑ᶠ p ∈ unweightedMassPairs j X t,
        ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) := by
  rw [unweightedMass_eq_sum, finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)]
  simp_rw [Finset.mul_sum]
  exact (Finset.sum_finset_product' _ _ _ fun p => by simp [unweightedMassPairs]).symm

/-- The unweighted terminal mass is nonnegative. -/
theorem unweightedMass_nonneg (j : ℕ) (X : ℝ) (t : ℚ) : 0 ≤ unweightedMass j X t := by
  rw [unweightedMass_eq_sum]
  refine Finset.sum_nonneg fun _ _ => mul_nonneg ?_ (Finset.sum_nonneg fun _ _ => ?_) <;>
    exact_mod_cast (Word.weight_pos _).le

end CollatzPosDens
