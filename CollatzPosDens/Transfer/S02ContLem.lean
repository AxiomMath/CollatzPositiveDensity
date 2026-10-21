/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Cont
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The continuation factor bounds a power of `400/83`

For each Fourier parameter index `ι : FIndex`, the continuation factor `ccont ι` is an upper bound
for the real power `(400/83) ^ Aexp ι`, where `Aexp ι` is the decay exponent.

Both sides are positive. For `ι = .o`, since `x ↦ x ^ 10000` is strictly increasing on `[0, ∞)`
and `10000 * Aexp .o = 21193`, the claim is equivalent to
`(400/83)^{21193} < (14009206687631/500000000000)^{10000}`, that is, to the integer comparison
`400^{21193} · 500000000000^{10000} < 14009206687631^{10000} · 83^{21193}`. For `ι = .b`, since
`10 * Aexp .b = 17`, the claim is equivalent to `(400/83)^{17} < (7245014059/500000000)^{10}`,
that is, to `400^{17} · 500000000^{10} < 7245014059^{10} · 83^{17}`. Both integer comparisons are
decided by evaluation.

## Main results

* `CollatzPosDens.rpow_Aexp_lt_ccont`: `(400/83 : ℝ) ^ (Aexp ι : ℝ) < ccont ι`.

## Implementation notes

The power `(400/83) ^ Aexp ι` is the real power `Real.rpow` with the exponent `Aexp ι` cast from
`ℚ` to `ℝ`, and `ccont ι` is cast from `ℚ` to `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The continuation factor `ccont ι` strictly exceeds the real power `(400/83) ^ Aexp ι`. -/
@[collatz_pos_dens "lem_s02_cont"]
theorem rpow_Aexp_lt_ccont (ι : FIndex) : (400 / 83 : ℝ) ^ (Aexp ι : ℝ) < (ccont ι : ℝ) := by
  cases ι with
  | o =>
    rw [Aexp_cast_o, ccont_cast_o]
    have key : ((400 / 83 : ℝ) ^ ((21193 / 10000 : ℝ))) ^ (10000 : ℕ) =
        (400 / 83 : ℝ) ^ (21193 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hint : (400 : ℕ) ^ 21193 * 500000000000 ^ 10000 <
        14009206687631 ^ 10000 * 83 ^ 21193 := by
      decide +kernel
    refine lt_of_pow_lt_pow_left₀ 10000 (by positivity) ?_
    rw [key, div_pow, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast hint
  | b =>
    rw [Aexp_cast_b, ccont_cast_b]
    have key : ((400 / 83 : ℝ) ^ ((17 / 10 : ℝ))) ^ (10 : ℕ) =
        (400 / 83 : ℝ) ^ (17 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hint : (400 : ℕ) ^ 17 * 500000000 ^ 10 < 7245014059 ^ 10 * 83 ^ 17 := by
      decide +kernel
    refine lt_of_pow_lt_pow_left₀ 10 (by positivity) ?_
    rw [key, div_pow, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast hint

end CollatzPosDens
