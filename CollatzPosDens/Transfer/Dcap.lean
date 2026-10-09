/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.B
public import CollatzPosDens.Transfer.Lb

/-!
# The scale cap `D_cap`

The scale cap is the natural number `D_cap := (B_* L_B)^2`, the square of the product of the
largest used scale `B_*` and its bit length `L_B`.

## Main definitions

* `CollatzPosDens.Dcap`: the scale cap `D_cap = (B_* L_B)^2`.

## Main results

* `CollatzPosDens.Dcap_def`: the defining formula `D_cap = (B_* L_B)^2`.
* `CollatzPosDens.cast_Dcap`: the same formula after casting into any semiring,
  e.g. `ℝ`.
* `CollatzPosDens.Dcap_pos`: `0 < D_cap`.
* `CollatzPosDens.Bstar_mul_LB_le_Dcap`: `B_* L_B ≤ D_cap`.

## Implementation notes

Since `B_*` is a closed natural number of more than seventeen thousand bits, `D_cap` is
declared irreducible, like `B_*` and `L_B`: it is used through `Dcap_def` and `cast_Dcap`,
never by evaluation. The square is taken through the auxiliary function
`DcapAux b l = (b l)^2` of free variables: checking `D_cap = (B_* L_B)^2` directly by
definitional unfolding makes the kernel try to evaluate the numeral `B_* L_B`, whereas
`DcapAux_def` is checked with `b` and `l` free.
-/

@[expose] public section

namespace CollatzPosDens

/-- The squared product `(b l)^2`; the scale cap is its value `D_cap = DcapAux B_* L_B`. -/
def DcapAux (b l : ℕ) : ℕ := (b * l) ^ 2

/-- The defining formula of `DcapAux`. -/
theorem DcapAux_def (b l : ℕ) : DcapAux b l = (b * l) ^ 2 := rfl

/-- The scale cap `D_cap := (B_* L_B)^2 ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_Dcap", irreducible]
noncomputable def Dcap : ℕ := DcapAux Bstar LB

/-- The defining formula of `D_cap`. -/
theorem Dcap_def : Dcap = (Bstar * LB) ^ 2 := by
  delta Dcap; exact DcapAux_def Bstar LB

/-- The defining formula of `D_cap`, cast into a semiring. -/
@[simp, norm_cast]
theorem cast_Dcap {R : Type*} [Semiring R] : (Dcap : R) = ((Bstar : R) * LB) ^ 2 := by
  rw [Dcap_def]; push_cast; rfl

/-- `D_cap` is positive. -/
theorem Dcap_pos : 0 < Dcap := by
  rw [Dcap_def]; exact pow_pos (Nat.mul_pos Bstar_pos LB_pos) 2

/-- `B_* L_B ≤ D_cap`. -/
theorem Bstar_mul_LB_le_Dcap : Bstar * LB ≤ Dcap := by
  have h (x : ℕ) : x ≤ x ^ 2 := Nat.le_self_pow two_ne_zero x
  rw [Dcap_def]
  exact h _

end CollatzPosDens
