/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.CharSum.ChPairFactorRange
public import CollatzPosDens.CharSum.ChEnvelopeRhs
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.CharSum.ChPascalMass

/-!
# The envelope series takes values in `[0, 1]`

Fix `n : ℕ` and a frequency `ξ : ResidueGroup n`. For all `k' j : ℕ` and `s : ℤ`, the sum of the
envelope series
`∑' b : Fin k' → ℤ, (∏ i, varpi (b i)) * ∏ i, chPairFactor n ξ (j + i) (s + ∑ l < i, b l) (b i)`
lies in `[0, 1]`. Each term lies between `0` and `∏ i, varpi (b i)`, since `varpi` is nonnegative
and `chPairFactor` takes values in `[0, 1]`; the envelope series is summable, and the series
`∑' b, ∏ i, varpi (b i)` has sum `1`, so comparing the two termwise gives the bounds.

## Main results

* `CollatzPosDens.tsum_chEnvelopeRhs_mem_Icc`: the sum of the envelope series lies in `[0, 1]`.

## Implementation notes

The coordinates of `b : Fin k' → ℤ` are indexed from `0`, so the factor of index `i` is
`chPairFactor n ξ (j + i) (s + ∑ l < i, b l) (b i)`. The bound holds for every `j : ℕ`, including
`j = 0`, so no hypothesis `j ≥ 1` is imposed.

## References

* [Mazur, *Collatz positive density*], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The envelope series has sum in `[0, 1]`: for all `k' j : ℕ` and `s : ℤ`, the sum over
`b : Fin k' → ℤ` of `(∏ i, varpi (b i)) * ∏ i, chPairFactor n ξ (j + i) (s + ∑ l < i, b l) (b i)`
lies in `[0, 1]`. -/
@[collatz_pos_dens "lem_ch_envelope_rhs_range"]
theorem tsum_chEnvelopeRhs_mem_Icc (n : ℕ) (ξ : ResidueGroup n) (k' j : ℕ) (s : ℤ) :
    (∑' b : Fin k' → ℤ, (∏ i, varpi (b i)) *
        ∏ i : Fin k', chPairFactor n ξ (j + i) (s + ∑ l ∈ Finset.Iio i, b l) (b i)) ∈
      Set.Icc (0 : ℝ) 1 := by
  have hvarpi (b : Fin k' → ℤ) : 0 ≤ ∏ i, varpi (b i) :=
    Finset.prod_nonneg fun i _ ↦ varpi_nonneg _
  refine ⟨tsum_nonneg fun b ↦ mul_nonneg (hvarpi b)
    (Finset.prod_nonneg fun i _ ↦ (chPairFactor_mem_Icc _ _ _ _ _).1), ?_⟩
  rw [← (hasSum_prod_varpi k').tsum_eq]
  refine (summable_chEnvelopeRhs n ξ k' j s).tsum_le_tsum (fun b ↦ ?_)
    (hasSum_prod_varpi k').summable
  exact mul_le_of_le_one_right (hvarpi b) <| Finset.prod_le_one₀
    (fun i _ ↦ (chPairFactor_mem_Icc _ _ _ _ _).1) (fun i _ ↦ (chPairFactor_mem_Icc _ _ _ _ _).2)

end CollatzPosDens
