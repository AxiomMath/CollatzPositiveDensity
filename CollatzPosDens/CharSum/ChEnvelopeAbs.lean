/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairProduct
public import CollatzPosDens.Characters.FxCharacterAbs
public import CollatzPosDens.Transfer.GeometricTotal

/-!
# Absolute convergence of the paired character series

For all integers `k ≥ 0`, `j ≥ 1` and `s ∈ ℤ`, the series `∑_{w ∈ ℤ_{≥1}^k} 2^{-A(w)} Ep(j, s; w)`
converges absolutely. Each `Ep(j, s; w)` is a finite product of values of the standard character
`e_n`, hence has modulus `1`; so the series of moduli is
`∑_{w ∈ ℤ_{≥1}^k} 2^{-A(w)} = 𝐩(ℤ_{≥1}^k) = 1`.

## Main results

* `CollatzPosDens.norm_chPairProduct`: `|Ep(j, s; w)| = 1`.
* `CollatzPosDens.summable_norm_chPairProduct_series`: the series
  `∑_{w ∈ ℤ_{≥1}^k} 2^{-A(w)} Ep(j, s; w)` converges absolutely.

## Implementation notes

Absolute convergence is stated as summability of the moduli of the terms, indexed by the subtype
of words of length `k`. The hypothesis `j ≥ 1` is not needed and is dropped.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.1.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The paired character product has modulus one: `|Ep(j, s; w)| = 1`. -/
theorem norm_chPairProduct (n : ℕ) (ξ : ResidueGroup n) :
    ∀ (j : ℕ) (s : ℤ) (w : Word), ‖chPairProduct n ξ j s w‖ = 1
  | _, _, [] => by simp
  | _, _, [_] => by simp
  | j, s, a₁ :: a₂ :: w => by
    rw [chPairProduct_cons_cons, norm_mul, fxChar_norm_eq_one,
      norm_chPairProduct n ξ (j + 1) (s + a₁ + a₂) w, one_mul]

/-- **Absolute convergence of the paired character series.** For all `k`, `j` and `s`, the
series `∑_{w ∈ ℤ_{≥1}^k} 2^{-A(w)} Ep(j, s; w)` converges absolutely. -/
@[collatz_pos_dens "lem_ch_envelope_abs"]
theorem summable_norm_chPairProduct_series (n : ℕ) (ξ : ResidueGroup n) (k j : ℕ) (s : ℤ) :
    Summable fun w : {w : Word | w.length = k} =>
      ‖(2⁻¹ : ℂ) ^ (w : Word).valSum * chPairProduct n ξ j s w‖ := by
  have h := ENNReal.summable_toReal (f := fun w : {w : Word | w.length = k} =>
    (w : Word).massWeight) (by rw [← geomMass_def, geomMass_setOf_length_eq]; simp)
  refine h.congr fun w => ?_
  simp [norm_chPairProduct, Word.massWeight, ENNReal.toReal_pow, ENNReal.toReal_inv]

end CollatzPosDens
