/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Dcap
public import CollatzPosDens.Transfer.S

/-!
# The scale threshold `D_sc`

The scale threshold `D_sc` is the natural number
$$D_{\mathrm{sc}} := 2 + P_* + D_{\mathrm{cap}} + (100 S_*)^2,$$
built from the final time `P_* = pStar`, the scale cap `D_cap = Dcap` and the far-gap scale
`S_* = sStar`.
It dominates each of its summands; in particular it is at least `2`, at least `P_*`, strictly
larger than `D_cap`, and at least `(100 S_*)^2`.

## Main definitions

* `CollatzPosDens.Dsc`: the scale threshold `D_sc = 2 + P_* + D_cap + (100 S_*)^2`.

## Main results

* `CollatzPosDens.Dsc_def`: the defining formula of `D_sc`.
* `CollatzPosDens.cast_Dsc`: the same formula cast into any semiring, e.g. `ℝ`.
* `CollatzPosDens.two_le_Dsc`, `CollatzPosDens.Dsc_pos`, `CollatzPosDens.Dsc_ne_zero`:
  `2 ≤ D_sc`, `0 < D_sc` and `D_sc ≠ 0`.
* `CollatzPosDens.pStar_le_Dsc`: `P_* ≤ D_sc`.
* `CollatzPosDens.Dcap_lt_Dsc`: `D_cap < D_sc`.
* `CollatzPosDens.sq_hundred_sStar_le_Dsc`: `(100 S_*)^2 ≤ D_sc`.

## Implementation notes

Since `P_*`, `D_cap` and `S_*` are closed natural numbers with thousands of digits, `D_sc` is
declared irreducible and is used only through `Dsc_def` and `cast_Dsc`, never by evaluation.
Its body is the value of the auxiliary function `DscAux p d s = 2 + p + d + (100 s)^2` of free
variables, so that the defining equation is checked with the arguments free and the kernel never
tries to normalise the closed sum to a numeral.
-/

@[expose] public section

namespace CollatzPosDens

/-- The sum `2 + p + d + (100 s)^2`; the scale threshold is `D_sc = DscAux P_* D_cap S_*`. -/
def DscAux (p d s : ℕ) : ℕ := 2 + p + d + (100 * s) ^ 2

/-- The defining formula of `DscAux`. -/
theorem DscAux_def (p d s : ℕ) : DscAux p d s = 2 + p + d + (100 * s) ^ 2 := rfl

/-- The scale threshold `D_sc := 2 + P_* + D_cap + (100 S_*)^2 ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_Dsc", irreducible]
noncomputable def Dsc : ℕ := DscAux pStar Dcap sStar

/-- The defining formula of `D_sc`. -/
theorem Dsc_def : Dsc = 2 + pStar + Dcap + (100 * sStar) ^ 2 := by
  delta Dsc; exact DscAux_def pStar Dcap sStar

/-- The defining formula of `D_sc`, cast into a semiring. -/
@[simp, norm_cast]
theorem cast_Dsc {R : Type*} [Semiring R] :
    (Dsc : R) = 2 + (pStar : R) + (Dcap : R) + (100 * (sStar : R)) ^ 2 := by
  rw [Dsc_def]; push_cast; rfl

/-- `2 ≤ D_sc`. -/
theorem two_le_Dsc : 2 ≤ Dsc := by
  rw [Dsc_def]; omega

/-- `D_sc` is positive. -/
theorem Dsc_pos : 0 < Dsc := lt_of_lt_of_le two_pos two_le_Dsc

/-- `D_sc ≠ 0`. -/
theorem Dsc_ne_zero : Dsc ≠ 0 := Dsc_pos.ne'

/-- `P_* ≤ D_sc`. -/
theorem pStar_le_Dsc : pStar ≤ Dsc := by
  rw [Dsc_def]; omega

/-- `D_cap < D_sc`. -/
theorem Dcap_lt_Dsc : Dcap < Dsc := by
  rw [Dsc_def]; omega

/-- `(100 S_*)^2 ≤ D_sc`. -/
theorem sq_hundred_sStar_le_Dsc : (100 * sStar) ^ 2 ≤ Dsc := by
  rw [Dsc_def]; omega

end CollatzPosDens
