/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Characters.FxCharacterInt
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Mixing.MxPushforward

/-!
# Fourier coefficients of the reference law at multiples of `3^j`

Write `G_n = ResidueGroup n = ℤ/3^nℤ`, `e_n = fxChar n` for its standard additive character,
`μ_n = refLaw n` for the reference law on `G_n`, `μ̂_n = refLawDft n` for its discrete Fourier
transform, and `π_{q,m} = residueReduction` for the reduction `G_q → G_m` with `m ≤ q`. For
`r, j ∈ ℕ` and `η ∈ G_{r+j}`,
$$\hat\mu_{r+j}(3^j\eta) = \hat\mu_r(\pi_{r+j,r}(\eta)).$$

The character `e_{r+j}` evaluated at `3^j z` only sees `z` modulo `3^r`:
`e_{r+j}(3^j z) = exp(2πi 3^j z̃ / 3^{r+j}) = exp(2πi z̃ / 3^r) = e_r(π_{r+j,r}(z))`.
Since `π_{r+j,r}` is a ring homomorphism, each term of `μ̂_{r+j}(3^j η)` is a function of
`π_{r+j,r}(y)`; grouping `y` into the fibres of `π_{r+j,r}` and applying the pushforward
identity `∑_{π_{r+j,r}(y) = x} μ_{r+j}(y) = μ_r(x)` gives `μ̂_r(π_{r+j,r}(η))`.

## Main results

* `CollatzPosDens.fxChar_three_pow_mul`: `e_{r+j}(3^j z) = e_r(π_{r+j,r}(z))`.
* `CollatzPosDens.refLawDft_three_pow_mul`: `μ̂_{r+j}(3^j η) = μ̂_r(π_{r+j,r}(η))`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.8.
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

open Complex Real Finset

/-- Scaling by `3^j` turns `e_{r+j}` into `e_r` composed with reduction:
`e_{r+j}(3^j z) = e_r(π_{r+j,r}(z))`. -/
theorem fxChar_three_pow_mul (r j : ℕ) (z : ResidueGroup (r + j)) :
    fxChar (r + j) (3 ^ j * z) = fxChar r (residueReduction (Nat.le_add_right r j) z) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  conv_rhs => rw [← ZMod.natCast_zmod_val z, residueReduction_natCast]
  have h : (3 : ResidueGroup (r + j)) ^ j * (z.val : ResidueGroup (r + j)) =
      ((3 ^ j * z.val : ℕ) : ResidueGroup (r + j)) := by push_cast; rfl
  rw [h, fxChar_natCast, fxChar_natCast]
  congr 1
  have h3 : (3 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show (3 : ℂ) ^ (r + j) = 3 ^ r * 3 ^ j from pow_add 3 r j]
  push_cast
  field_simp

/-- **Reduction of Fourier coefficients.** For `r, j ∈ ℕ` and `η ∈ G_{r+j}`,
`μ̂_{r+j}(3^j η) = μ̂_r(π_{r+j,r}(η))`. -/
@[collatz_pos_dens "lem_mx_dft_reduction"]
theorem refLawDft_three_pow_mul (r j : ℕ) (η : ResidueGroup (r + j)) :
    refLawDft (r + j) (3 ^ j * η) =
      refLawDft r (residueReduction (Nat.le_add_right r j) η) := by
  set p := residueReduction (Nat.le_add_right r j)
  have hterm : ∀ y : ResidueGroup (r + j),
      ((refLaw (r + j) y).toReal : ℂ) * fxChar (r + j) (-(3 ^ j * η * y)) =
        ((refLaw (r + j) y).toReal : ℂ) * fxChar r (-(p η * p y)) := by
    intro y
    rw [mul_assoc, ← mul_neg, fxChar_three_pow_mul, map_neg, map_mul]
  rw [refLawDft_apply, refLawDft_apply]
  simp_rw [hterm]
  rw [← Finset.sum_fiberwise Finset.univ p]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sum_refLaw_residueReduction_eq (Nat.le_add_right r j) x,
    ENNReal.toReal_sum (fun y _ => refLaw_ne_top _ y),
    Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [(Finset.mem_filter.1 hy).2]

end CollatzPosDens
