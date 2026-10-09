/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldWords
public import CollatzPosDens.Renewal.RnPascal
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The holding-time law `η`

For a lattice point `(j, l)` in the set `𝒫 = ℤ_{≥1} × ℤ` of `CollatzPosDens.bkPoints`, the
holding-time law is `η(j, l) = ∑_{c ∈ 𝒞_{j,l}} ∏_{i=1}^{j} ϖ(c_i)`, the sum running over the hold
words `𝒞_{j,l} = CollatzPosDens.holdWords j l` (words of length `j` with letters at least `2`, only
the last letter in `{4, 5}`, and letter sum `l`) and `ϖ = CollatzPosDens.varpi` being the Pascal
holding-time weight.

## Main definitions

* `CollatzPosDens.holdLaw j l`: the holding-time law `η(j, l)`.

## Main results

* `CollatzPosDens.holdLaw_def`: the defining sum.
* `CollatzPosDens.holdLaw_nonneg`: `0 ≤ η(j, l)`.
* `CollatzPosDens.holdLaw_zero`: the value at `j = 0` (outside `𝒫`).

## Implementation notes

The sum over `𝒞_{j,l}` is a `tsum` over the subtype of the set `holdWords j l`. This set is
finite, so the `tsum` is a finite sum. As for `holdWords`, the index `j` ranges over all of `ℕ`
rather than over `j ≥ 1`; only the values with `j ≥ 1` carry meaning.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The holding-time law `η(j, l) = ∑_{c ∈ 𝒞_{j,l}} ∏_{i=1}^{j} ϖ(c_i)`. -/
@[collatz_pos_dens "def_rn_hold"]
noncomputable def holdLaw (j : ℕ) (l : ℤ) : ℝ :=
  ∑' c : holdWords j l, ∏ i, varpi (c.1 i)

/-- `η(j, l)` is the sum over the hold words `c ∈ 𝒞_{j,l}` of `∏ i, ϖ(c_i)`. -/
theorem holdLaw_def (j : ℕ) (l : ℤ) :
    holdLaw j l = ∑' c : holdWords j l, ∏ i, varpi (c.1 i) :=
  rfl

/-- The holding-time law is nonnegative. -/
theorem holdLaw_nonneg (j : ℕ) (l : ℤ) : 0 ≤ holdLaw j l :=
  tsum_nonneg fun _ ↦ Finset.prod_nonneg fun _ _ ↦ varpi_nonneg _

/-- At `j = 0` (outside `𝒫`), `η(0, l)` is `1` if `l = 0` and `0` otherwise. -/
theorem holdLaw_zero (l : ℤ) : holdLaw 0 l = if l = 0 then 1 else 0 := by
  have h := holdWords_zero l
  rw [holdLaw_def]
  split_ifs at h ⊢ with hl
  · rw [h]
    exact (tsum_univ (f := fun c : Fin 0 → ℤ ↦ ∏ i, varpi (c i))).trans (by simp)
  · rw [h]
    simp

end CollatzPosDens
