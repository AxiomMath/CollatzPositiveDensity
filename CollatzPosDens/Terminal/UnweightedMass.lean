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
# The unweighted terminal mass `Υ_{n,X}(M)`

For `n : ℕ`, a real `X` and a starting point `M`, the unweighted terminal mass is the double sum
$$\Upsilon_{n,X}(M) = \sum_{h \in \mathcal H_n(M)} \omega(h)
  \sum_{w} \omega(w),$$
where the inner sum runs over the words `w ∈ 𝒲(b_n, u_h, 1)` satisfying the length condition
`Λ_{b_n,u_h}(w)` and admissible from the endpoint `R_h` of `h`; here `u_h = u_{n,X}(R_h)` is the
terminal shift of `h` and `ω(h) = ω(ŵ(h))` is the weight of its concatenated word. The pairs
`(h, w)` occurring in this double sum are the *counted pairs* of `Υ_{n,X}(M)`. Both sums are
finite, since `𝓗_n(M)` and `𝒲(b, u, K)` are finite sets.

## Main definitions

* `CollatzPosDens.unweightedMassWords n X M h`: the words `w` of the inner sum attached to `h`.
* `CollatzPosDens.unweightedMassPairs n X M`: the set of counted pairs `(h, w)`.
* `CollatzPosDens.unweightedMass n X M`: the unweighted terminal mass `Υ_{n,X}(M)`.

## Main results

* `CollatzPosDens.mem_unweightedMassWords`, `CollatzPosDens.mem_unweightedMassPairs`:
  the defining conditions of the index sets.
* `CollatzPosDens.unweightedMassWords_finite`, `CollatzPosDens.unweightedMassPairs_finite`:
  the index sets are finite.
* `CollatzPosDens.unweightedMass_eq_sum`: `Υ_{n,X}(M)` as an iterated `Finset` sum.
* `CollatzPosDens.unweightedMass_eq_finsum_pairs`: `Υ_{n,X}(M)` as the sum of `ω(h) ω(w)`
  over the counted pairs.
* `CollatzPosDens.unweightedMass_nonneg`: `0 ≤ Υ_{n,X}(M)`.

## Implementation notes

The sums are `finsum`s over sets, genuine finite sums by `unweightedMassWords_finite`; the set of
counted pairs is a `Set` with a finiteness lemma, so `(unweightedMassPairs_finite n X M).toFinset`
is the corresponding `Finset`. The mass is real-valued; the weights `ω` are rational and are cast
to `ℝ`. The terminal shift `u_h` is a natural number, cast to `ℤ` to index the first-crossing
family. The starting point `M` is taken in `ℚ`, as in `centralHistories`, and neither its oddness
and positivity nor the positivity of `X` is needed to state the definition.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- The words of the inner sum of `Υ_{n,X}(M)` attached to a history `h`: the words
`w ∈ 𝒲(b_n, u_h, 1)` with `Λ_{b_n,u_h}(w)` that are admissible from the endpoint `R_h`. -/
def unweightedMassWords (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) : Set Word :=
  {w | w ∈ firstCrossing (scale n) (historyShift n X M h) 1 ∧
    LengthOk (scale n) (historyShift n X M h) w ∧ Admissible (historyEndpoint M h) w}

/-- The *counted pairs* of `Υ_{n,X}(M)`: the pairs `(h, w)` with `h ∈ 𝓗_n(M)`,
`w ∈ 𝒲(b_n, u_h, 1)`, `Λ_{b_n,u_h}(w)` and `w` admissible from `R_h`. -/
@[collatz_pos_dens "def_unweighted_mass"]
def unweightedMassPairs (n : ℕ) (X : ℝ) (M : ℚ) : Set ((Fin n → Word) × Word) :=
  {p | p.1 ∈ centralHistories M n ∧ p.2 ∈ unweightedMassWords n X M p.1}

/-- The unweighted terminal mass
`Υ_{n,X}(M) = ∑_{h ∈ 𝓗_n(M)} ω(h) ∑_w ω(w)`, the inner sum over `w ∈ 𝒲(b_n, u_h, 1)` with
`Λ_{b_n,u_h}(w)` and `w` admissible from `R_h`. -/
@[collatz_pos_dens "def_unweighted_mass"]
noncomputable def unweightedMass (n : ℕ) (X : ℝ) (M : ℚ) : ℝ :=
  ∑ᶠ h ∈ centralHistories M n,
    ((concatWord h).weight : ℝ) * ∑ᶠ w ∈ unweightedMassWords n X M h, (w.weight : ℝ)

/-- Membership in the inner index set of `Υ_{n,X}(M)`. -/
theorem mem_unweightedMassWords {X : ℝ} {M : ℚ} {h : Fin n → Word} {w : Word} :
    w ∈ unweightedMassWords n X M h ↔
      w ∈ firstCrossing (scale n) (historyShift n X M h) 1 ∧
        LengthOk (scale n) (historyShift n X M h) w ∧ Admissible (historyEndpoint M h) w :=
  Iff.rfl

/-- The defining condition of a counted pair of `Υ_{n,X}(M)`. -/
theorem mem_unweightedMassPairs {X : ℝ} {M : ℚ} {h : Fin n → Word} {w : Word} :
    (h, w) ∈ unweightedMassPairs n X M ↔
      h ∈ centralHistories M n ∧ w ∈ firstCrossing (scale n) (historyShift n X M h) 1 ∧
        LengthOk (scale n) (historyShift n X M h) w ∧ Admissible (historyEndpoint M h) w :=
  Iff.rfl

/-- The inner index set of `Υ_{n,X}(M)` is finite. -/
theorem unweightedMassWords_finite (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) :
    (unweightedMassWords n X M h).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

/-- The set of counted pairs of `Υ_{n,X}(M)` is finite. -/
theorem unweightedMassPairs_finite (n : ℕ) (X : ℝ) (M : ℚ) :
    (unweightedMassPairs n X M).Finite :=
  ((centralHistories_finite M n).biUnion fun h _ =>
    (unweightedMassWords_finite n X M h).image (Prod.mk h)).subset
    fun p hp => Set.mem_biUnion hp.1 ⟨p.2, hp.2, rfl⟩

/-- `Υ_{n,X}(M)` as an iterated `Finset` sum. -/
theorem unweightedMass_eq_sum (n : ℕ) (X : ℝ) (M : ℚ) :
    unweightedMass n X M = ∑ h ∈ (centralHistories_finite M n).toFinset,
      ((concatWord h).weight : ℝ) *
        ∑ w ∈ (unweightedMassWords_finite n X M h).toFinset, (w.weight : ℝ) := by
  rw [unweightedMass,
    finsum_mem_eq_finite_toFinset_sum _ (centralHistories_finite M n)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassWords_finite n X M h)]

/-- `Υ_{n,X}(M)` is the sum of `ω(h) ω(w)` over its counted pairs `(h, w)`. -/
theorem unweightedMass_eq_finsum_pairs (n : ℕ) (X : ℝ) (M : ℚ) :
    unweightedMass n X M =
      ∑ᶠ p ∈ unweightedMassPairs n X M,
        ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) := by
  rw [unweightedMass_eq_sum, finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)]
  simp_rw [Finset.mul_sum]
  exact (Finset.sum_finset_product' _ _ _ fun p => by simp [unweightedMassPairs]).symm

/-- The unweighted terminal mass is nonnegative. -/
theorem unweightedMass_nonneg (n : ℕ) (X : ℝ) (M : ℚ) : 0 ≤ unweightedMass n X M :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => mul_nonneg (by exact_mod_cast
    (Word.weight_pos _).le) (finsum_nonneg fun _ => finsum_nonneg fun _ => by
      exact_mod_cast (Word.weight_pos _).le)

end CollatzPosDens
