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

Fix a Fourier index `ι ∈ 𝔍`, a level `n ≥ 1` and a residue `ξ ∈ G_n`. For an entry point
`e ∈ 𝒫`, the event `Low^e(ι)` consists of the fresh atoms `a ∈ 𝒜_n` whose weighted white count
up to time `P_*(ι) - 1` is at most `T_*(ι)`:
`Low^e(ι) = {a ∈ 𝒜_n : N^e_{P_*(ι)-1}(a) ≤ T_*(ι)}`.

## Main definitions

* `CollatzPosDens.trLow ι n ξ e`: the event `Low^e(ι)`.

## Main results

* `CollatzPosDens.mem_trLow`: the membership criterion.
* `CollatzPosDens.trLow_subset_trAtoms`: `Low^e(ι) ⊆ 𝒜_n`.
* `CollatzPosDens.trWhiteCount_le_of_mem_trLow`,
  `CollatzPosDens.lt_trWhiteCount_of_notMem_trLow`: the count bound inside `Low^e(ι)`, and its
  failure for an atom of `𝒜_n` outside it.

## Implementation notes

The count `N^e_p(a)` is real-valued and `T_*(ι) ∈ ℕ` is cast to `ℝ`. The time `P_*(ι) - 1` is
natural subtraction, which is exact since `P_*(ι) ≥ 1` (`one_le_pStar`). The set lives in the
ambient type `(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n` and carries the condition `a ∈ 𝒜_n`
explicitly. The hypotheses `n ≥ 1` and `e ∈ 𝒫` play no role in the definition and are dropped,
so `trLow ι n ξ e` is defined for every `n` and every `e : ℤ × ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The low weighted white count event
`Low^e(ι) = {a ∈ 𝒜_n : N^e_{P_*(ι)-1}(a) ≤ T_*(ι)}`. -/
@[collatz_pos_dens "def_tr_low"]
def trLow (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) :
    Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ trWhiteCount n ξ e a (pStar ι - 1) ≤ (tStar ι : ℝ)}

variable {ι : FIndex} {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ}
  {a : (ℕ × ℤ) × List (List ℤ × ℤ)}

/-- Membership in `Low^e(ι)`. -/
theorem mem_trLow :
    a ∈ trLow ι n ξ e ↔
      a ∈ trAtoms n ∧ trWhiteCount n ξ e a (pStar ι - 1) ≤ (tStar ι : ℝ) :=
  Iff.rfl

/-- `Low^e(ι) ⊆ 𝒜_n`. -/
theorem trLow_subset_trAtoms (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) :
    trLow ι n ξ e ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- Inside `Low^e(ι)`, `N^e_{P_*(ι)-1}(a) ≤ T_*(ι)`. -/
theorem trWhiteCount_le_of_mem_trLow (ha : a ∈ trLow ι n ξ e) :
    trWhiteCount n ξ e a (pStar ι - 1) ≤ (tStar ι : ℝ) :=
  ha.2

/-- An atom of `𝒜_n` outside `Low^e(ι)` has `T_*(ι) < N^e_{P_*(ι)-1}(a)`. -/
theorem lt_trWhiteCount_of_notMem_trLow (ha : a ∈ trAtoms n) (hl : a ∉ trLow ι n ξ e) :
    (tStar ι : ℝ) < trWhiteCount n ξ e a (pStar ι - 1) :=
  not_le.1 fun h => hl ⟨ha, h⟩

end CollatzPosDens
