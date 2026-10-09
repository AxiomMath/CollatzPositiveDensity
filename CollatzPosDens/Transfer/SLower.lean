/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S
public import CollatzPosDens.Transfer.PBits

/-!
# A lower bound for the far-gap scale `S_*`

Since `S_* = 2^{36} P_*` and `2^{17450} ≤ P_*`, we get `2^{17486} ≤ S_*`, and in particular
`S_* > 2^{365}`.

## Main results

* `CollatzPosDens.two_pow_le_sStar`: `2^{17486} ≤ S_*`.
* `CollatzPosDens.two_pow_lt_sStar`: `2^m < S_*` for `m < 17486`.
* `CollatzPosDens.two_pow_365_lt_sStar`: `2^{365} < S_*`.

## Implementation notes

The powers of two are compared through monotonicity of `n ↦ 2^n`, so no large power is evaluated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `2^{36 + 17450} ≤ S_*`. -/
theorem two_pow_le_sStar : 2 ^ (36 + 17450) ≤ sStar := by
  rw [sStar_def, pow_add]
  exact Nat.mul_le_mul_left _ two_pow_le_pStar

/-- `2^m < S_*` for every `m < 36 + 17450`. -/
theorem two_pow_lt_sStar {m : ℕ} (hm : m < 36 + 17450) : 2 ^ m < sStar :=
  (pow_lt_pow_right₀ one_lt_two hm).trans_le two_pow_le_sStar

/-- `S_* > 2^{365}`. -/
@[collatz_pos_dens "lem_s02_S_lower"]
theorem two_pow_365_lt_sStar : 2 ^ 365 < sStar :=
  two_pow_lt_sStar (by omega)

end CollatzPosDens
