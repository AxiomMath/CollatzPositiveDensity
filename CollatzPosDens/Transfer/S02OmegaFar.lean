/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02ROmega

/-!
# The far-gap threshold `Ω_far`

The far-gap threshold of the transfer argument at the Fourier parameter index `ι ∈ {o, b}` is
the natural number `Ω_far(ι) := R_Ω(ι)^2`, the square of the far-gap scale `R_Ω(ι)`. A gap
`ω > Ω_far(ι)` is called far; for such a gap `√ω > R_Ω(ι)`.

## Main definitions

* `CollatzPosDens.omegaFar`: the far-gap threshold `Ω_far(ι) = R_Ω(ι)^2`.

## Main results

* `CollatzPosDens.omegaFar_def`: the defining formula `Ω_far(ι) = R_Ω(ι)^2`.
* `CollatzPosDens.cast_omegaFar`: the same formula after casting into any semiring, e.g. `ℝ`.
* `CollatzPosDens.omegaFar_pos`: `0 < Ω_far(ι)`.
* `CollatzPosDens.sqrt_omegaFar`: `⌊√Ω_far(ι)⌋ = R_Ω(ι)`.
* `CollatzPosDens.ROmega_le_omegaFar`: `R_Ω(ι) ≤ Ω_far(ι)`.
* `CollatzPosDens.sq_le_omegaFar_o`: `((1231/4) V_*(o))^2 ≤ Ω_far(o)` in any linearly ordered
  field.
* `CollatzPosDens.omegaFar_b`: `Ω_far(b) = (45 V_*(b))^2`.

## Implementation notes

`R_Ω(ι)` is a closed natural number of many bits, so `Ω_far(ι)` is used through `omegaFar_def`
and `cast_omegaFar`, never by evaluation.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The far-gap threshold `Ω_far(ι) := R_Ω(ι)^2 ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_Omega_far"]
noncomputable def omegaFar (ι : FIndex) : ℕ := ROmega ι ^ 2

/-- The defining formula of `Ω_far(ι)`. -/
theorem omegaFar_def (ι : FIndex) : omegaFar ι = ROmega ι ^ 2 := by
  unfold omegaFar
  rfl

/-- The defining formula of `Ω_far(ι)`, cast into a semiring. -/
@[simp, norm_cast]
theorem cast_omegaFar {R : Type*} [Semiring R] (ι : FIndex) :
    (omegaFar ι : R) = (ROmega ι : R) ^ 2 := by
  rw [omegaFar_def, Nat.cast_pow]

/-- `Ω_far(ι)` is positive. -/
theorem omegaFar_pos (ι : FIndex) : 0 < omegaFar ι := by
  rw [omegaFar_def]
  exact pow_pos (ROmega_pos ι) 2

/-- The integer square root of `Ω_far(ι)` is `R_Ω(ι)`. -/
theorem sqrt_omegaFar (ι : FIndex) : Nat.sqrt (omegaFar ι) = ROmega ι := by
  rw [omegaFar_def, sq, Nat.sqrt_eq]

/-- `R_Ω(ι) ≤ Ω_far(ι)`. -/
theorem ROmega_le_omegaFar (ι : FIndex) : ROmega ι ≤ omegaFar ι := by
  rw [omegaFar_def]
  exact Nat.le_self_pow two_ne_zero _

/-- `((1231/4) V_*(o))^2 ≤ Ω_far(o)` in any linearly ordered field. -/
theorem sq_le_omegaFar_o {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ((1231 / 4 : K) * Vstar .o) ^ 2 ≤ omegaFar .o := by
  rw [cast_omegaFar]
  have h0 : (0 : K) ≤ (1231 / 4 : K) * Vstar .o := by positivity
  exact pow_le_pow_left₀ h0 le_ROmega_o 2

/-- `Ω_far(b) = (45 V_*(b))^2`. -/
theorem omegaFar_b : omegaFar .b = (45 * Vstar .b) ^ 2 := by
  rw [omegaFar_def, ROmega_b]

end CollatzPosDens
