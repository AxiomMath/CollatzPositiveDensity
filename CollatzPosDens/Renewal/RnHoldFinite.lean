/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldWords
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Finiteness of the hold words

For every `j : ℕ` and `l : ℤ` the set `holdWords j l` of hold words is finite. Indeed a word
`c ∈ holdWords j l` has `2 ≤ c i` for every `i` and `∑ i, c i = l`; since all letters are
nonnegative, each letter is at most the sum, so `2 ≤ c i ≤ l` for every `i`, and `holdWords j l`
lies in the finite box `[2, l]^j`.

## Main results

* `CollatzPosDens.holdWords_subset_pi_Icc`: `holdWords j l ⊆ [2, l]^j`.
* `CollatzPosDens.holdWords_finite`: `holdWords j l` is finite.

## Implementation notes

The statement is proved for every `j : ℕ`, including `j = 0`: the argument does not use
`j ≥ 1`, and `holdWords` is defined for all `j`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- Every letter of a hold word in `holdWords j l` lies in `[2, l]`. -/
theorem holdWords_subset_pi_Icc (j : ℕ) (l : ℤ) :
    holdWords j l ⊆ Set.univ.pi fun _ : Fin j ↦ Set.Icc (2 : ℤ) l := by
  intro c hc
  have hge := holdWords_two_le hc
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  refine fun i ↦ ⟨hge i, ?_⟩
  rw [← holdWords_sum_eq hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : 0 ≤ ∑ k ∈ Finset.univ.erase i, c k :=
    Finset.sum_nonneg fun k _ ↦ by have := hge k; omega
  omega

/-- For every `j` and `l`, the set of hold words `holdWords j l` is finite. -/
@[collatz_pos_dens "lem_rn_hold_finite"]
theorem holdWords_finite (j : ℕ) (l : ℤ) : (holdWords j l).Finite :=
  (Set.Finite.pi fun _ ↦ Set.finite_Icc _ _).subset (holdWords_subset_pi_Icc j l)

end CollatzPosDens
