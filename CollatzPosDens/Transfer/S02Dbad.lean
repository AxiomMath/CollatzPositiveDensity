/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.S02PBits
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# The bad-advance threshold `D_bad`

At each Fourier parameter index `ι ∈ {o, b}` the bad-advance threshold is the natural number
$$D_{\mathrm{bad}}(ι) := 2^{21} (P_*(ι) + 64),$$
where `P_*(ι) = CollatzPosDens.pStar ι` is the final time at index `ι`.

From the exact values `P_*(o) = 17140454471732661035095372256` and `P_*(b) = 63701995`, both at
least `2^22 - 64 = 4194240`, we get `P_*(ι) + 64 ≥ 2^22` and hence `2^43 ≤ D_bad(ι)` at both
indices. Exactly, `D_bad(o) = 35946138376303093555072330251632640` and
`D_bad(b) = 2^21 · 63702059 = 133592900435968`.

## Main definitions

* `CollatzPosDens.Dbad`: the bad-advance threshold `D_bad(ι) = 2^21 (P_*(ι) + 64) : ℕ`.

## Main results

* `CollatzPosDens.Dbad_def`: the defining formula of `D_bad(ι)`.
* `CollatzPosDens.cast_Dbad`: the defining formula cast into a semiring, e.g. `ℝ`.
* `CollatzPosDens.two_pow_43_le_Dbad`: the lower bound `2^43 ≤ D_bad(ι)`.

## Implementation notes

The final time `P_*(ι)` is a closed natural number of up to `94` bits, so `D_bad` is never
evaluated; it is irreducible and is used through `Dbad_def` and `cast_Dbad`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The bad-advance threshold `D_bad(ι) := 2^21 (P_*(ι) + 64) ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_Dbad", irreducible]
noncomputable def Dbad (ι : FIndex) : ℕ := 2 ^ 21 * (pStar ι + 64)

/-- The defining formula of `D_bad(ι)`. -/
theorem Dbad_def (ι : FIndex) : Dbad ι = 2 ^ 21 * (pStar ι + 64) := by
  unfold Dbad
  rfl

/-- The defining formula of `D_bad(ι)`, cast into a semiring. -/
@[simp, norm_cast]
theorem cast_Dbad {R : Type*} [Semiring R] (ι : FIndex) :
    (Dbad ι : R) = 2 ^ 21 * ((pStar ι : R) + 64) := by
  rw [Dbad_def, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]

/-- **Lower size of the bad-advance threshold.** `2^43 ≤ D_bad(ι)` for every index `ι`. -/
@[collatz_pos_dens "lem_s02_Dbad_lower"]
theorem two_pow_43_le_Dbad (ι : FIndex) : 2 ^ 43 ≤ Dbad ι := by
  have h : 2 ^ 22 ≤ pStar ι + 64 := by
    cases ι
    · rw [pStar_o]; norm_num
    · rw [pStar_b]; norm_num
  rw [Dbad_def, show (2 : ℕ) ^ 43 = 2 ^ 21 * 2 ^ 22 by norm_num]
  exact Nat.mul_le_mul_left _ h

end CollatzPosDens
