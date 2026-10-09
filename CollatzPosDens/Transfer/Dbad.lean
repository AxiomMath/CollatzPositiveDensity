/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Aexp

/-!
# The bad-advance threshold `D_bad`

The bad-advance threshold is the positive rational number
$$D_{\mathrm{bad}} := (2^{53} A_*)^2 + 2^{53} (P_* + 65),$$
built from the decay exponent `A_* = 10241/4096` (`CollatzPosDens.Aexp`) and the final time
`P_*` (`CollatzPosDens.pStar`). Since $2^{53} A_* = 2^{41} \cdot 10241$ is an integer, so is
`D_bad`.

## Main definitions

* `CollatzPosDens.Dbad`: the bad-advance threshold
  `D_bad = (2^53 A_*)^2 + 2^53 (P_* + 65) : ℚ`.

## Main results

* `CollatzPosDens.Dbad_def`: the defining formula of `D_bad`.
* `CollatzPosDens.Dbad_eq`: the same formula with `A_*` evaluated,
  $D_{\mathrm{bad}} = (2^{41} \cdot 10241)^2 + 2^{53} (P_* + 65)$.
* `CollatzPosDens.cast_Dbad`: the defining formula after casting into a division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Dbad_pos`: `0 < D_bad`.
* `CollatzPosDens.sq_two_pow_mul_Aexp_le_Dbad`,
  `CollatzPosDens.two_pow_mul_pStar_add_le_Dbad`: each summand is at most `D_bad`.

## Implementation notes

The final time `P_*` is irreducible, so `D_bad` is never evaluated; it is used through
`Dbad_def`, `Dbad_eq` and `cast_Dbad`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The bad-advance threshold `D_bad := (2^53 A_*)^2 + 2^53 (P_* + 65) ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_Dbad"]
noncomputable def Dbad : ℚ := (2 ^ 53 * Aexp) ^ 2 + 2 ^ 53 * ((pStar : ℚ) + 65)

/-- The defining formula of `D_bad`. -/
theorem Dbad_def : Dbad = (2 ^ 53 * Aexp) ^ 2 + 2 ^ 53 * ((pStar : ℚ) + 65) := rfl

/-- The defining formula of `D_bad` with `A_* = 10241/4096` evaluated:
`2^53 A_* = 2^41 · 10241`. -/
theorem Dbad_eq : Dbad = (2 ^ 41 * 10241) ^ 2 + 2 ^ 53 * ((pStar : ℚ) + 65) := by
  rw [Dbad_def, Aexp_eq]; norm_num

/-- The defining formula of `D_bad`, cast into a division ring of characteristic zero. -/
@[simp, norm_cast]
theorem cast_Dbad {K : Type*} [DivisionRing K] [CharZero K] :
    (Dbad : K) = (2 ^ 53 * (Aexp : K)) ^ 2 + 2 ^ 53 * ((pStar : K) + 65) := by
  rw [Dbad_def]; push_cast; rfl

/-- The square summand `(2^53 A_*)^2` is at most `D_bad`. -/
theorem sq_two_pow_mul_Aexp_le_Dbad : (2 ^ 53 * Aexp) ^ 2 ≤ Dbad :=
  le_add_of_nonneg_right (by positivity)

/-- The summand `2^53 (P_* + 65)` is at most `D_bad`. -/
theorem two_pow_mul_pStar_add_le_Dbad : 2 ^ 53 * ((pStar : ℚ) + 65) ≤ Dbad :=
  le_add_of_nonneg_left (sq_nonneg _)

/-- `D_bad` is positive. -/
theorem Dbad_pos : 0 < Dbad := by
  rw [Dbad_def]; positivity

end CollatzPosDens
