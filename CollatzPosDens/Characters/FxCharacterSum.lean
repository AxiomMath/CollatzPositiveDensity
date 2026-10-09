/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Characters.FxOffsetLaw
public import CollatzPosDens.Characters.FxCharacterAbs
public import CollatzPosDens.Transfer.GeometricTotal

/-!
# The Fourier coefficients of the reference law as a character sum

For every `n ∈ ℕ` and `ξ ∈ G_n`,
`μ̂_n(ξ) = ∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} e_n(-[off(w)]_n ξ)`, the series converging absolutely.

By `CollatzPosDens.refLaw_eq_tsum_off`, `μ_n(y) = ∑_w 2^{-A(w)} [[off(w)]_n = y]`, and these
values are finite. Every term of the resulting double series has modulus at most `2^{-A(w)}`, and
`∑_w 2^{-A(w)} = 𝐩(ℤ_{≥1}^n) = 1`, so the two summations may be exchanged; for fixed `w` only
`y = [off(w)]_n` contributes.

## Main results

* `CollatzPosDens.summable_norm_fxCharSum`: the series converges absolutely.
* `CollatzPosDens.refLawDft_eq_tsum_off`: `μ̂_n(ξ) = ∑_w 2^{-A(w)} e_n(-[off(w)]_n ξ)`.

## Implementation notes

The set `ℤ_{≥1}^n` is the set of words of length `n`, and `[off(w)]_n` is the dyadic reduction
`dyadicRed n` applied to `off(w) ∈ ℤ[1/2]`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

private theorem summable_inv_two_pow_valSum (n : ℕ) :
    Summable fun w : {w : Word | w.length = n} => ((2 : ℝ) ^ (w : Word).valSum)⁻¹ := by
  have h := ENNReal.summable_toReal (f := fun w : {w : Word | w.length = n} =>
    (w : Word).massWeight) (by rw [← geomMass_def, geomMass_setOf_length_eq]; simp)
  simpa [Word.massWeight, ENNReal.toReal_inv, ENNReal.toReal_pow] using h

/-- **Absolute convergence.** The series `∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} e_n(-[off(w)]_n ξ)`
converges absolutely. -/
@[collatz_pos_dens "lem_fx_character_sum"]
theorem summable_norm_fxCharSum (n : ℕ) (ξ : ResidueGroup n) :
    Summable fun w : {w : Word | w.length = n} =>
      ‖((2 : ℂ) ^ (w : Word).valSum)⁻¹ *
        fxChar n (-(dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ * ξ))‖ := by
  simpa [fxChar_norm_eq_one] using summable_inv_two_pow_valSum n

/-- **Character-sum formula.** For every `n ∈ ℕ` and `ξ ∈ G_n`,
`μ̂_n(ξ) = ∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} e_n(-[off(w)]_n ξ)`. -/
@[collatz_pos_dens "lem_fx_character_sum"]
theorem refLawDft_eq_tsum_off (n : ℕ) (ξ : ResidueGroup n) :
    refLawDft n ξ = ∑' w : {w : Word | w.length = n},
      ((2 : ℂ) ^ (w : Word).valSum)⁻¹ *
        fxChar n (-(dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ * ξ)) := by
  set r : {w : Word | w.length = n} → ResidueGroup n :=
    fun w => dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩
  have hs := summable_inv_two_pow_valSum n
  have hterm : ∀ y : ResidueGroup n, ((refLaw n y).toReal : ℂ) * fxChar n (-(ξ * y)) =
      ∑' w : {w : Word | w.length = n},
        (if r w = y then ((2 : ℂ) ^ (w : Word).valSum)⁻¹ else 0) * fxChar n (-(ξ * y)) := by
    intro y
    rw [refLaw_eq_tsum_off, ENNReal.tsum_toReal_eq (fun w => by split_ifs <;> simp),
      Complex.ofReal_tsum, ← tsum_mul_right]
    refine tsum_congr fun w => ?_
    split_ifs <;> simp_all
  rw [refLawDft_apply, Finset.sum_congr rfl fun y _ => hterm y, ← Summable.tsum_finsetSum]
  · refine tsum_congr fun w => ?_
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), mul_comm ξ]
  · intro y _
    refine Summable.of_norm_bounded hs fun w => ?_
    split_ifs <;> simp

end CollatzPosDens
