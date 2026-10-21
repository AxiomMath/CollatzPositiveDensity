/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3NarrowTable
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith

/-!
# The maximal packet deficit

Fix integers `c` and `o`. A *packet family* for `(c,o)` is a finite set `𝒦` of pairs `(i,t)` of
integers with `0 ≤ i`, `i + t ≤ c - 1` and `(o - i, t) ∈ T'` (the index set of the narrow packet
envelope table `U'`), whose index sets `{i, …, i + t - 1}` are pairwise disjoint. The *maximal
packet deficit* is
`a_{c,o} = max_𝒦 ∑_{(i,t) ∈ 𝒦} t (1 - U'_{o-i,t})`,
the maximum over the finitely many packet families for `(c,o)`; the empty family gives `0`.

## Main definitions

* `CollatzPosDens.c3PacketCandidates c o`: the finite set of pairs `(i,t)` that may occur in a
  packet family for `(c,o)`.
* `CollatzPosDens.IsC3PacketFamily c o K`: `K` is a packet family for `(c,o)`.
* `CollatzPosDens.c3PacketFamilies c o`: the finite set of all packet families for `(c,o)`.
* `CollatzPosDens.c3PacketWeight o K`: the sum `∑_{(i,t) ∈ K} t (1 - U'_{o-i,t})`.
* `CollatzPosDens.c3PacketDeficit c o`: the maximal packet deficit `a_{c,o}`.

## Main results

* `CollatzPosDens.mem_c3PacketCandidates`: membership in the candidate set.
* `CollatzPosDens.mem_c3PacketFamilies`: `K ∈ c3PacketFamilies c o ↔ IsC3PacketFamily c o K`.
* `CollatzPosDens.isC3PacketFamily_iff_pairwiseDisjoint`: the disjointness condition as
  `Set.PairwiseDisjoint`.
* `CollatzPosDens.c3PacketWeight_le_c3PacketDeficit`: every packet family has weight at most
  `a_{c,o}`.
* `CollatzPosDens.exists_c3PacketDeficit_eq`: some packet family attains `a_{c,o}`.
* `CollatzPosDens.c3PacketDeficit_nonneg`: `0 ≤ a_{c,o}`.

## Implementation notes

The deficit is used only for `3 ≤ c ≤ 16` and `1 ≤ o ≤ c`; the definition here is total in the
integers `c` and `o`. A packet family is a subset of the finite candidate set
`c3PacketCandidates c o`, which is the image of a filter of `T'`; the families are therefore the
members of a filtered powerset, and `a_{c,o}` is a `Finset.sup'` over this nonempty finite set of
rationals. Disjointness is stated pairwise on the finset, so that it is decidable.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The pairs `(i,t)` that may occur in a packet family for `(c,o)`: those with `0 ≤ i`,
`i + t ≤ c - 1` and `(o - i, t) ∈ T'`. It is computed as the image of a filter of `T'` under
`(s,t) ↦ (o - s, t)`. -/
def c3PacketCandidates (c o : ℤ) : Finset (ℤ × ℤ) :=
  (c3NarrowTableDomain.filter fun st => 0 ≤ o - st.1 ∧ o - st.1 + st.2 ≤ c - 1).image
    fun st => (o - st.1, st.2)

/-- A pair `(i,t)` lies in `c3PacketCandidates c o` if and only if `0 ≤ i`, `i + t ≤ c - 1` and
`(o - i, t) ∈ T'`. -/
theorem mem_c3PacketCandidates {c o : ℤ} {p : ℤ × ℤ} :
    p ∈ c3PacketCandidates c o ↔
      0 ≤ p.1 ∧ p.1 + p.2 ≤ c - 1 ∧ (o - p.1, p.2) ∈ c3NarrowTableDomain := by
  obtain ⟨i, t⟩ := p
  simp only [c3PacketCandidates, Finset.mem_image, Finset.mem_filter, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨s, t', ⟨hT, h0, h1⟩, rfl, rfl⟩
    refine ⟨h0, h1, ?_⟩
    simpa using hT
  · rintro ⟨h0, h1, hT⟩
    exact ⟨o - i, t, ⟨hT, by omega, by omega⟩, by omega, rfl⟩

/-- `K` is a *packet family* for `(c,o)`: every `(i,t) ∈ K` has `0 ≤ i`, `i + t ≤ c - 1` and
`(o - i, t) ∈ T'`, and the index sets `{i, …, i + t - 1}` of distinct members are disjoint. -/
def IsC3PacketFamily (c o : ℤ) (K : Finset (ℤ × ℤ)) : Prop :=
  (∀ p ∈ K, 0 ≤ p.1 ∧ p.1 + p.2 ≤ c - 1 ∧ (o - p.1, p.2) ∈ c3NarrowTableDomain) ∧
    ∀ p ∈ K, ∀ q ∈ K, p ≠ q → Disjoint (Finset.Ico p.1 (p.1 + p.2)) (Finset.Ico q.1 (q.1 + q.2))

/-- Being a packet family is decidable. -/
instance (c o : ℤ) (K : Finset (ℤ × ℤ)) : Decidable (IsC3PacketFamily c o K) := by
  unfold IsC3PacketFamily; infer_instance

/-- `K` is a packet family for `(c,o)` if and only if every member satisfies the candidate
conditions and the index sets `{i, …, i + t - 1}` of its members are pairwise disjoint. -/
theorem isC3PacketFamily_iff_pairwiseDisjoint {c o : ℤ} {K : Finset (ℤ × ℤ)} :
    IsC3PacketFamily c o K ↔
      (∀ p ∈ K, 0 ≤ p.1 ∧ p.1 + p.2 ≤ c - 1 ∧ (o - p.1, p.2) ∈ c3NarrowTableDomain) ∧
        (K : Set (ℤ × ℤ)).PairwiseDisjoint fun p => Finset.Ico p.1 (p.1 + p.2) := by
  unfold IsC3PacketFamily Set.PairwiseDisjoint Set.Pairwise
  simp only [Finset.mem_coe, Function.onFun]

/-- Every packet family for `(c,o)` is contained in `c3PacketCandidates c o`. -/
theorem IsC3PacketFamily.subset_c3PacketCandidates {c o : ℤ} {K : Finset (ℤ × ℤ)}
    (hK : IsC3PacketFamily c o K) : K ⊆ c3PacketCandidates c o :=
  fun p hp => mem_c3PacketCandidates.2 (hK.1 p hp)

/-- The empty set is a packet family for `(c,o)`. -/
theorem isC3PacketFamily_empty (c o : ℤ) : IsC3PacketFamily c o ∅ := by
  simp [IsC3PacketFamily]

/-- The finite set of all packet families for `(c,o)`. -/
def c3PacketFamilies (c o : ℤ) : Finset (Finset (ℤ × ℤ)) :=
  (c3PacketCandidates c o).powerset.filter (IsC3PacketFamily c o)

/-- `K ∈ c3PacketFamilies c o` if and only if `K` is a packet family for `(c,o)`. -/
theorem mem_c3PacketFamilies {c o : ℤ} {K : Finset (ℤ × ℤ)} :
    K ∈ c3PacketFamilies c o ↔ IsC3PacketFamily c o K := by
  simp only [c3PacketFamilies, Finset.mem_filter, Finset.mem_powerset, and_iff_right_iff_imp]
  exact IsC3PacketFamily.subset_c3PacketCandidates

/-- The empty family belongs to `c3PacketFamilies c o`. -/
theorem empty_mem_c3PacketFamilies (c o : ℤ) : ∅ ∈ c3PacketFamilies c o :=
  mem_c3PacketFamilies.2 (isC3PacketFamily_empty c o)

/-- The set of packet families for `(c,o)` is nonempty. -/
theorem c3PacketFamilies_nonempty (c o : ℤ) : (c3PacketFamilies c o).Nonempty :=
  ⟨∅, empty_mem_c3PacketFamilies c o⟩

/-- The weight `∑_{(i,t) ∈ K} t (1 - U'_{o-i,t})` of a finite set `K` of pairs. -/
def c3PacketWeight (o : ℤ) (K : Finset (ℤ × ℤ)) : ℚ :=
  ∑ p ∈ K, (p.2 : ℚ) * (1 - c3NarrowTable (o - p.1) p.2)

/-- The weight of the empty family is `0`. -/
@[simp] theorem c3PacketWeight_empty (o : ℤ) : c3PacketWeight o ∅ = 0 := by
  simp [c3PacketWeight]

/-- The weight of a packet family is nonnegative. -/
theorem IsC3PacketFamily.c3PacketWeight_nonneg {c o : ℤ} {K : Finset (ℤ × ℤ)}
    (hK : IsC3PacketFamily c o K) : 0 ≤ c3PacketWeight o K := by
  refine Finset.sum_nonneg fun p hp => mul_nonneg ?_ ?_
  · have := (mem_c3NarrowTableDomain_bounds (hK.1 p hp).2.2).2.2.1
    exact_mod_cast (by omega : (0 : ℤ) ≤ p.2)
  · linarith [c3NarrowTable_lt_one (o - p.1) p.2]

/-- The *maximal packet deficit* `a_{c,o} = max_𝒦 ∑_{(i,t) ∈ 𝒦} t (1 - U'_{o-i,t})`, the maximum
over the packet families `𝒦` for `(c,o)` (the empty family giving `0`). -/
@[collatz_pos_dens "def_c3_packet_deficit"]
def c3PacketDeficit (c o : ℤ) : ℚ :=
  (c3PacketFamilies c o).sup' (c3PacketFamilies_nonempty c o) (c3PacketWeight o)

/-- The weight of every packet family for `(c,o)` is at most `a_{c,o}`. -/
theorem c3PacketWeight_le_c3PacketDeficit {c o : ℤ} {K : Finset (ℤ × ℤ)}
    (hK : IsC3PacketFamily c o K) : c3PacketWeight o K ≤ c3PacketDeficit c o :=
  Finset.le_sup' (c3PacketWeight o) (mem_c3PacketFamilies.2 hK)

/-- Some packet family attains the maximal packet deficit. -/
theorem exists_c3PacketDeficit_eq (c o : ℤ) :
    ∃ K, IsC3PacketFamily c o K ∧ c3PacketWeight o K = c3PacketDeficit c o := by
  obtain ⟨K, hK, h⟩ :=
    Finset.exists_mem_eq_sup' (c3PacketFamilies_nonempty c o) (c3PacketWeight o)
  exact ⟨K, mem_c3PacketFamilies.1 hK, h.symm⟩

/-- The maximal packet deficit is nonnegative. -/
theorem c3PacketDeficit_nonneg (c o : ℤ) : 0 ≤ c3PacketDeficit c o := by
  simpa using c3PacketWeight_le_c3PacketDeficit (isC3PacketFamily_empty c o)

/-- `a_{c,o} ≤ x` if and only if every packet family for `(c,o)` has weight at most `x`. -/
theorem c3PacketDeficit_le_iff {c o : ℤ} {x : ℚ} :
    c3PacketDeficit c o ≤ x ↔ ∀ K, IsC3PacketFamily c o K → c3PacketWeight o K ≤ x := by
  simp only [c3PacketDeficit, Finset.sup'_le_iff, mem_c3PacketFamilies]

end CollatzPosDens
