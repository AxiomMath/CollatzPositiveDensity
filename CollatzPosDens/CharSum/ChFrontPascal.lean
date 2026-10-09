/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.CharSum.ChEnvelope
public import CollatzPosDens.CharSum.ChPairExpansion
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Characters.FxCharacterSum
public import CollatzPosDens.Renewal.RnPascal

/-!
# The Pascal-type envelope of the Fourier coefficients of the reference law

Fix `n : ℕ`, write `J = ⌊n / 2⌋`, and let `ξ ∈ G_n`. Then
`|μ̂_n(ξ)| ≤ ∑_{b ∈ ℤ^J} ∏_{i=1}^J ϖ(b_i) ∏_{i=1}^J Fp(i, b_1 + ⋯ + b_{i-1}, b_i)`.

The proof writes `μ̂_n(ξ)` as a sum over words by `refLawDft_eq_tsum_off`, rewrites each
character value as a `chPairProduct` by `fxChar_neg_dyadicRed_off_mul_eq_chPairProduct`, and
applies `norm_tsum_chPairProduct_le`.

## Main results

* `CollatzPosDens.norm_refLawDft_le_tsum_chPairFactor`: the envelope bound for `μ̂_n(ξ)`.

## Implementation notes

`ℤ^J` is `Fin (n / 2) → ℤ` with indices `i = 0, …, J - 1`, so the factor of index `i` is
`Fp(i + 1, ∑_{l < i} b_l, b_i)`. No hypothesis `n ≥ 1` is needed.
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- **Front Pascal bound.** For every `ξ ∈ G_n`, writing `J = ⌊n / 2⌋`,
`|μ̂_n(ξ)| ≤ ∑_{b ∈ ℤ^J} ∏_i ϖ(b_i) ∏_i Fp(i, b_1 + ⋯ + b_{i-1}, b_i)`. -/
@[collatz_pos_dens "lem_ch_front_pascal"]
theorem norm_refLawDft_le_tsum_chPairFactor (n : ℕ) (ξ : ResidueGroup n) :
    ‖refLawDft n ξ‖ ≤
      ∑' b : Fin (n / 2) → ℤ, (∏ i, varpi (b i)) *
        ∏ i : Fin (n / 2), chPairFactor n ξ (i + 1) (∑ l ∈ Iio i, b l) (b i) := by
  have h := norm_tsum_chPairProduct_le n ξ n 1 0
  simp only [zero_add, add_comm 1] at h
  refine le_of_eq_of_le ?_ h
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
