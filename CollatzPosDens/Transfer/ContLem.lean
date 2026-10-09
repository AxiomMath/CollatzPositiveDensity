/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.Cont
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The continuation factor bounds `(400/83)^{A_*}`

The continuation factor `c_cont = 511/10` is an upper bound for the real power
`(400/83)^{A_*}`, where `A_* = 10241/4096` is the decay exponent.

Since both sides are positive and `x ↦ x ^ 4096` is strictly increasing on `[0, ∞)`, and since
`4096 A_* = 10241`, the claim is equivalent to `(400/83)^{10241} < (511/10)^{4096}`, that is, to
the integer comparison `400^{10241} · 10^{4096} < 511^{4096} · 83^{10241}`, which is decided by
evaluation.

## Main results

* `CollatzPosDens.rpow_Aexp_lt_ccont`: `(400/83 : ℝ) ^ (A_* : ℝ) < c_cont`.

## Implementation notes

The power `(400/83)^{A_*}` is the real power `Real.rpow` with the exponent `A_*` cast from `ℚ`
to `ℝ`, and `c_cont` is cast from `ℚ` to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The continuation factor dominates the power `(400/83)^{A_*}`. -/
@[collatz_pos_dens "lem_s02_cont"]
theorem rpow_Aexp_lt_ccont : (400 / 83 : ℝ) ^ (Aexp : ℝ) < (ccont : ℝ) := by
  rw [Aexp_cast, ccont_cast]
  have key : ((400 / 83 : ℝ) ^ ((10241 / 4096 : ℝ))) ^ (4096 : ℕ) =
      (400 / 83 : ℝ) ^ (10241 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hint : (400 : ℕ) ^ 10241 * 10 ^ 4096 < 511 ^ 4096 * 83 ^ 10241 := by decide +kernel
  have hR := (Nat.cast_lt (α := ℝ)).mpr hint
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_ofNat, Nat.cast_ofNat, Nat.cast_ofNat] at hR
  refine lt_of_pow_lt_pow_left₀ 4096 (by norm_num) ?_
  rw [key, div_pow, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  exact hR

end CollatzPosDens
