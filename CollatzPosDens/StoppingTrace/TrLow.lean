/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrWhiteCount

/-!
# The low weighted white count event

Fix a level `n` and a residue `ξ : ResidueGroup n`. For a pair `e : ℤ × ℤ`, the event `Low^e`
consists of the fresh atoms `a ∈ 𝒜_n` (the set `trAtoms n`) whose weighted white count
`N^e_p(a) = trWhiteCount n ξ e a p` at time `P_* - 1` is at most `T_*`, where `P_* = pStar`
and `T_* = tStar`:
`Low^e = {a ∈ 𝒜_n : N^e_{P_*-1}(a) ≤ T_*}`.

## Main definitions

* `CollatzPosDens.trLow n ξ e`: the event `Low^e`.

## Main results

* `CollatzPosDens.mem_trLow`: the membership criterion.
* `CollatzPosDens.trLow_subset_trAtoms`: `Low^e ⊆ 𝒜_n`.
* `CollatzPosDens.trWhiteCount_le_of_mem_trLow`,
  `CollatzPosDens.lt_trWhiteCount_of_notMem_trLow`: the count bound inside `Low^e`, and its
  failure for an atom of `𝒜_n` outside it.

## Implementation notes

The count `N^e_p(a)` is real-valued and `T_* ∈ ℕ` is cast to `ℝ`. The time `P_* - 1` is
natural subtraction, which is exact since `P_* ≥ 1`. The set lives in the ambient type
`(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n` and carries the condition `a ∈ 𝒜_n` explicitly. The
definition is stated for every level `n` and every pair `e`, with no positivity hypothesis on
`n` and no restriction of `e` to entry points.

## References

* [Mazur, *Collatz positive density*], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- The low weighted white count event `Low^e = {a ∈ 𝒜_n : N^e_{P_*-1}(a) ≤ T_*}`. -/
@[collatz_pos_dens "def_tr_low"]
def trLow (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ trWhiteCount n ξ e a (pStar - 1) ≤ (tStar : ℝ)}

variable {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)}

/-- Membership in `Low^e`. -/
@[simp]
theorem mem_trLow :
    a ∈ trLow n ξ e ↔ a ∈ trAtoms n ∧ trWhiteCount n ξ e a (pStar - 1) ≤ (tStar : ℝ) :=
  Iff.rfl

/-- `Low^e ⊆ 𝒜_n`. -/
theorem trLow_subset_trAtoms (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) :
    trLow n ξ e ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- Inside `Low^e`, `N^e_{P_*-1}(a) ≤ T_*`. -/
theorem trWhiteCount_le_of_mem_trLow (ha : a ∈ trLow n ξ e) :
    trWhiteCount n ξ e a (pStar - 1) ≤ (tStar : ℝ) :=
  ha.2

/-- An atom of `𝒜_n` outside `Low^e` has `T_* < N^e_{P_*-1}(a)`. -/
theorem lt_trWhiteCount_of_notMem_trLow (ha : a ∈ trAtoms n) (hl : a ∉ trLow n ξ e) :
    (tStar : ℝ) < trWhiteCount n ξ e a (pStar - 1) :=
  not_le.1 fun h => hl ⟨ha, h⟩

end CollatzPosDens
