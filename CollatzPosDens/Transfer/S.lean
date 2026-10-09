/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar

/-!
# The far-gap scale `S_*`

The far-gap scale is the natural number
$$S_* := 2^{36} P_*,$$
where `P_* = CollatzPosDens.pStar` is the final time of the schedule `CollatzPosDens.schedule`.
It is positive and strictly exceeds `P_*`.

## Main definitions

* `CollatzPosDens.sStar`: the far-gap scale `S_* = 2^36 P_*`.

## Main results

* `CollatzPosDens.sStar_def`: the defining formula `S_* = 2^36 P_*`.
* `CollatzPosDens.sStar_cast`: the same formula in any semiring, e.g. in `ℝ`.
* `CollatzPosDens.sStar_pos`: `0 < S_*`.
* `CollatzPosDens.pStar_lt_sStar`: `P_* < S_*`.
* `CollatzPosDens.pStar_le_sStar`: `P_* ≤ S_*`.

## Implementation notes

Since `pStar` is irreducible, the product `2 ^ 36 * pStar` is never evaluated; facts about
`sStar` are derived from `sStar_def` and the lemmas about `pStar`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The far-gap scale `S_* := 2^36 P_*`. -/
@[collatz_pos_dens "def_s02_S"]
noncomputable def sStar : ℕ := 2 ^ 36 * pStar

/-- The defining formula of `S_*`. -/
theorem sStar_def : sStar = 2 ^ 36 * pStar := rfl

/-- The defining formula of `S_*`, cast to a semiring (typically `ℝ`). -/
theorem sStar_cast {R : Type*} [Semiring R] : (sStar : R) = 2 ^ 36 * (pStar : R) := by
  rw [sStar_def, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- `S_*` is positive. -/
theorem sStar_pos : 0 < sStar :=
  Nat.mul_pos (by positivity) pStar_pos

/-- `P_*` is strictly smaller than `S_*`. -/
theorem pStar_lt_sStar : pStar < sStar :=
  lt_mul_of_one_lt_left pStar_pos (by norm_num)

/-- `P_*` is at most `S_*`. -/
theorem pStar_le_sStar : pStar ≤ sStar := pStar_lt_sStar.le

end CollatzPosDens
