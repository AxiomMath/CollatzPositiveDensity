/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Order.Bounds.Basic

/-!
# Bounded policies

A *bounded policy* is a set `W ⊆ ℕ × ℕ × ℕ` of triples `(r, h, c)` for which there is a single
`K ∈ ℕ` such that every `(r, h, c) ∈ W` satisfies `c ≥ 2` and `h + c ≤ K`. A triple `(r, h, c)`
is read as prescribing a continuation of length `c` at depth `h`.

## Main definitions

* `CollatzPosDens.IsBoundedPolicy W`: `W` is a bounded policy.

## Main results

* `CollatzPosDens.IsBoundedPolicy.two_le`: every triple of a bounded policy has `c ≥ 2`.
* `CollatzPosDens.IsBoundedPolicy.mono`: a subset of a bounded policy is a bounded policy.
* `CollatzPosDens.IsBoundedPolicy.union`: the union of two bounded policies is one.
* `CollatzPosDens.isBoundedPolicy_iff_bddAbove`: `W` is a bounded policy iff all its triples have
  `c ≥ 2` and the values `h + c` are bounded above.

## Implementation notes

Triples `(r, h, c)` are encoded as `ℕ × ℕ × ℕ` with `p.1 = r`, `p.2.1 = h`, `p.2.2 = c`.
The first coordinate `r` is unconstrained, so a bounded policy need not be finite.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A set `W ⊆ ℕ × ℕ × ℕ` of triples `(r, h, c)` is a *bounded policy* if there is `K ∈ ℕ` such
that every `(r, h, c) ∈ W` satisfies `2 ≤ c` and `h + c ≤ K`. -/
@[collatz_pos_dens "def_tr_tree_policy"]
def IsBoundedPolicy (W : Set (ℕ × ℕ × ℕ)) : Prop :=
  ∃ K : ℕ, ∀ p ∈ W, 2 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ K

namespace IsBoundedPolicy

variable {W W' : Set (ℕ × ℕ × ℕ)}

/-- Every triple `(r, h, c)` of a bounded policy has `c ≥ 2`. -/
theorem two_le (hW : IsBoundedPolicy W) {p : ℕ × ℕ × ℕ} (hp : p ∈ W) : 2 ≤ p.2.2 := by
  obtain ⟨K, hK⟩ := hW
  exact (hK p hp).1

/-- Every triple `(r, h, c)` of a bounded policy has `c ≥ 1`. -/
theorem pos (hW : IsBoundedPolicy W) {p : ℕ × ℕ × ℕ} (hp : p ∈ W) : 0 < p.2.2 :=
  Nat.lt_of_lt_of_le (by decide) (hW.two_le hp)

/-- A subset of a bounded policy is a bounded policy. -/
theorem mono (hW : IsBoundedPolicy W) (h : W' ⊆ W) : IsBoundedPolicy W' := by
  obtain ⟨K, hK⟩ := hW
  exact ⟨K, fun p hp => hK p (h hp)⟩

/-- The union of two bounded policies is a bounded policy. -/
theorem union (hW : IsBoundedPolicy W) (hW' : IsBoundedPolicy W') :
    IsBoundedPolicy (W ∪ W') := by
  obtain ⟨K, hK⟩ := hW
  obtain ⟨K', hK'⟩ := hW'
  refine ⟨max K K', fun p hp => ?_⟩
  rcases hp with hp | hp
  · exact ⟨(hK p hp).1, (hK p hp).2.trans (le_max_left _ _)⟩
  · exact ⟨(hK' p hp).1, (hK' p hp).2.trans (le_max_right _ _)⟩

/-- The intersection of a bounded policy with any set is a bounded policy. -/
theorem inter_left (hW : IsBoundedPolicy W) (S : Set (ℕ × ℕ × ℕ)) :
    IsBoundedPolicy (W ∩ S) :=
  hW.mono Set.inter_subset_left

end IsBoundedPolicy

/-- The empty set is a bounded policy. -/
theorem isBoundedPolicy_empty : IsBoundedPolicy ∅ :=
  ⟨0, fun _ hp => hp.elim⟩

/-- `W` is a bounded policy iff all its triples `(r, h, c)` have `c ≥ 2` and the values `h + c`
are bounded above. -/
theorem isBoundedPolicy_iff_bddAbove {W : Set (ℕ × ℕ × ℕ)} :
    IsBoundedPolicy W ↔
      (∀ p ∈ W, 2 ≤ p.2.2) ∧ BddAbove ((fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2) '' W) := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨fun p hp => (hK p hp).1, K, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (hK p hp).2
  · rintro ⟨h2, K, hK⟩
    exact ⟨K, fun p hp => ⟨h2 p hp, hK ⟨p, hp, rfl⟩⟩⟩

end CollatzPosDens
