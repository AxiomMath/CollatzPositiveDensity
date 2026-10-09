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
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.CharSum.ChPascalMass

/-!
# Convergence of the envelope series

Fix `n` and a frequency `ξ : ResidueGroup n`. For all `k' j : ℕ` and `s : ℤ`, the series of
nonnegative terms
`∑_{b : Fin k' → ℤ} ∏_{i < k'} ϖ(b_i) ∏_{i < k'} Fp(j + i, s + ∑_{l < i} b_l, b_i)`
converges, where `ϖ` is `varpi` and `Fp` is `chPairFactor n ξ`. Every value of `chPairFactor`
lies in `[0, 1]` and `varpi` is nonnegative, so each term lies between `0` and `∏_i ϖ(b_i)`; the
series converges by comparison with the series of `∏_i ϖ(b_i)`, whose sum is `1`
(`hasSum_prod_varpi`).

## Main results

* `CollatzPosDens.summable_chEnvelopeRhs`: the envelope series converges.

## Implementation notes

The indices run over `Fin k'`, so `i = 0, …, k' - 1`, and the factor of index `i` is
`Fp(j + i, s + ∑_{l < i} b_l, b_i)`. No lower bound on `j` is needed.

## References

* [Mazur, *Collatz positive density*], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The envelope series converges.** For all `k'`, `j` and `s`, the nonnegative series
`∑_{b : Fin k' → ℤ} ∏_i ϖ(b_i) ∏_i Fp(j + i, s + ∑_{l < i} b_l, b_i)` converges, where `ϖ` is
`varpi` and `Fp` is `chPairFactor n ξ`. -/
@[collatz_pos_dens "lem_ch_envelope_rhs"]
theorem summable_chEnvelopeRhs (n : ℕ) (ξ : ResidueGroup n) (k' j : ℕ) (s : ℤ) :
    Summable fun b : Fin k' → ℤ ↦
      (∏ i, varpi (b i)) *
        ∏ i : Fin k', chPairFactor n ξ (j + i) (s + ∑ l ∈ Finset.Iio i, b l) (b i) := by
  refine (hasSum_prod_varpi k').summable.of_nonneg_of_le (fun b ↦ ?_) (fun b ↦ ?_)
  · exact mul_nonneg (Finset.prod_nonneg fun i _ ↦ varpi_nonneg _)
      (Finset.prod_nonneg fun i _ ↦ (chPairFactor_mem_Icc _ _ _ _ _).1)
  · refine mul_le_of_le_one_right (Finset.prod_nonneg fun i _ ↦ varpi_nonneg _) ?_
    exact Finset.prod_le_one₀ (fun i _ ↦ (chPairFactor_mem_Icc _ _ _ _ _).1)
      (fun i _ ↦ (chPairFactor_mem_Icc _ _ _ _ _).2)

end CollatzPosDens
