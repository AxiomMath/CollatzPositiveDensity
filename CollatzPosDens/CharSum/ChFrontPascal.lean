/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.CharSum.ChEnvelope
public import CollatzPosDens.CharSum.ChEnvelopeRhs
public import CollatzPosDens.CharSum.ChFpFormula
public import CollatzPosDens.CharSum.ChPairExpansion
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Characters.FxCharacterSum
public import CollatzPosDens.Renewal.RnPascal

/-!
# The Pascal-type envelope of the Fourier coefficients of the reference law

Fix `n : ℕ`, write `J = ⌊n / 2⌋`, and let `ξ ∈ G_n`. Then
`|μ̂_n(ξ)| ≤ ∑_{b ∈ ℤ^J} ∏_{i=1}^J ϖ(b_i) ∏_{i=1}^J φ_{b_i}((i, b_1 + ⋯ + b_i))`,
the series on the right being a convergent series of nonnegative terms.

By the character-sum formula, `μ̂_n(ξ) = ∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} e_n(-[off(w)]_n ξ)`; pairing
the letters with `(j, s) = (1, 0)` turns each character value into `Ep(1, 0; w)`, and the
envelope bound with `(k, j, s) = (n, 1, 0)` bounds `|μ̂_n(ξ)|` by the convergent series
`∑_b ∏_i ϖ(b_i) ∏_i Fp(i, b_1 + ⋯ + b_{i-1}, b_i)`. Each pair factor
`Fp(i, b_1 + ⋯ + b_{i-1}, b_i)` equals the raw factor `φ_{b_i}((i, b_1 + ⋯ + b_i))`, so the two
series agree term by term.

## Main results

* `CollatzPosDens.norm_refLawDft_le_tsum_chPairFactor`: the envelope bound for `μ̂_n(ξ)`,
  together with the summability of the bounding series.

## Implementation notes

`ℤ^J` is `Fin (n / 2) → ℤ` with indices `i = 0, …, J - 1`, so the factor of index `i` is
`φ_{b_i}((i + 1, ∑_{l ≤ i} b_l))`. The bound holds for every `n`, including `n = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- The pair factors along `b` are the raw factors at the partial sums of `b`. -/
private theorem chPairFactor_iio_eq_chRawFactor_iic (n : ℕ) (ξ : ResidueGroup n) {J : ℕ}
    (b : Fin J → ℤ) (i : Fin J) :
    chPairFactor n ξ (1 + i) (0 + ∑ l ∈ Iio i, b l) (b i) =
      chRawFactor n ξ (b i) ((i : ℤ) + 1, ∑ l ∈ Iic i, b l) := by
  rw [chPairFactor_eq_norm_sum_exp_bkTheta, zero_add, ← Iio_insert, sum_insert (by simp),
    add_comm (b i)]
  push_cast
  rw [add_comm (1 : ℤ)]

/-- **Front Pascal bound.** For every `ξ ∈ G_n`, writing `J = ⌊n / 2⌋`,
`|μ̂_n(ξ)| ≤ ∑_{b ∈ ℤ^J} ∏_i ϖ(b_i) ∏_i φ_{b_i}((i, b_1 + ⋯ + b_i))`, the series on the right
being convergent. -/
@[collatz_pos_dens "lem_ch_front_pascal"]
theorem norm_refLawDft_le_tsum_chPairFactor (n : ℕ) (ξ : ResidueGroup n) :
    ‖refLawDft n ξ‖ ≤
      ∑' b : Fin (n / 2) → ℤ, (∏ i, varpi (b i)) *
        ∏ i : Fin (n / 2), chRawFactor n ξ (b i) ((i : ℤ) + 1, ∑ l ∈ Iic i, b l) ∧
    Summable fun b : Fin (n / 2) → ℤ ↦ (∏ i, varpi (b i)) *
        ∏ i : Fin (n / 2), chRawFactor n ξ (b i) ((i : ℤ) + 1, ∑ l ∈ Iic i, b l) := by
  have hterm : (fun b : Fin (n / 2) → ℤ ↦ (∏ i, varpi (b i)) *
        ∏ i : Fin (n / 2), chRawFactor n ξ (b i) ((i : ℤ) + 1, ∑ l ∈ Iic i, b l)) =
      fun b ↦ (∏ i, varpi (b i)) *
        ∏ i : Fin (n / 2), chPairFactor n ξ (1 + i) (0 + ∑ l ∈ Iio i, b l) (b i) := by
    funext b
    simp only [chPairFactor_iio_eq_chRawFactor_iic]
  rw [hterm]
  refine ⟨?_, summable_chEnvelopeRhs n ξ (n / 2) 1 0⟩
  refine le_of_eq_of_le ?_ (norm_tsum_chPairProduct_le n ξ n 1 0)
  rw [refLawDft_eq_tsum_off]
  congr 1
  refine tsum_congr fun w => ?_
  rw [inv_pow, ← fxChar_neg_dyadicRed_off_mul_eq_chPairProduct n ξ le_rfl 0 w]
  have hw : (⟨off w, off_mem_dyadicRationals w⟩ : dyadicRationals) =
      ⟨(3 : ℚ) ^ (2 * (1 - 1)) * 2 ^ (-(0 : ℤ)) * off w,
        three_pow_mul_two_zpow_mul_off_mem_dyadicRationals 1 0 w⟩ :=
    Subtype.ext (by simp)
  rw [hw]

end CollatzPosDens
