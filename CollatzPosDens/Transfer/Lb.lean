/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.B
public import CollatzPosDens.Transfer.Bitlength

/-!
# The bit length of the largest scale

The natural number `L_B := bl(B_*)` is the bit length of the largest used scale `B_*`. It is
characterized by `2^(L_B - 1) ≤ B_* < 2^L_B`, and it enters the capacity threshold
`CollatzPosDens.Dcap = (B_* L_B)^2`.

## Main definitions

* `CollatzPosDens.LB`: the bit length `L_B = bl(B_*)` of the largest scale.

## Main results

* `CollatzPosDens.LB_def`: the defining formula `L_B = bl(B_*)`.
* `CollatzPosDens.LB_le_iff`: `L_B ≤ k ↔ B_* < 2^k`.
* `CollatzPosDens.lt_LB_iff`: `k < L_B ↔ 2^k ≤ B_*`.
* `CollatzPosDens.LB_pos`: `0 < L_B`.
* `CollatzPosDens.Bstar_lt_two_pow_LB`: `B_* < 2^L_B`.
* `CollatzPosDens.two_pow_LB_sub_one_le_Bstar`: `2^(L_B - 1) ≤ B_*`.

## Implementation notes

`B_*` is a closed natural number of more than seventeen thousand bits, so `L_B`, like `B_*`,
is declared irreducible: it is used through `LB_def` and the bounds of this file, never by
unfolding. Its numerical value `L_B = 17484` is `CollatzPosDens.LB_eq`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The bit length of the largest scale, `L_B := bl(B_*) ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_Lb", irreducible]
noncomputable def LB : ℕ := bitLength Bstar

/-- The defining formula `L_B = bl(B_*)`. -/
theorem LB_def : LB = bitLength Bstar := by
  delta LB; rfl

/-- `L_B ≤ k ↔ B_* < 2^k`. -/
theorem LB_le_iff {k : ℕ} : LB ≤ k ↔ Bstar < 2 ^ k := by
  rw [LB_def]; exact bitLength_le_iff

/-- `k < L_B ↔ 2^k ≤ B_*`. -/
theorem lt_LB_iff {k : ℕ} : k < LB ↔ 2 ^ k ≤ Bstar := by
  rw [LB_def]; exact bitLength_lt_iff

/-- `L_B` is positive, since `B_*` is. -/
theorem LB_pos : 0 < LB := by
  rw [LB_def]; exact bitLength_pos.2 Bstar_pos

/-- `B_* < 2^L_B`. -/
theorem Bstar_lt_two_pow_LB : Bstar < 2 ^ LB := LB_le_iff.1 le_rfl

/-- `2^(L_B - 1) ≤ B_*`. -/
theorem two_pow_LB_sub_one_le_Bstar : 2 ^ (LB - 1) ≤ Bstar :=
  lt_LB_iff.1 (Nat.sub_lt LB_pos Nat.one_pos)

end CollatzPosDens
