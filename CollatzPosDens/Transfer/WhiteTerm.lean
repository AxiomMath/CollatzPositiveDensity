/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.Lc
public import CollatzPosDens.Transfer.PW
public import CollatzPosDens.Transfer.Z
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The many-white term

We prove `exp (-101 z_*) (400/83)^{A_*} < 1 / P_W`, where `z_*` is the white Fourier penalty,
`A_*` the decay exponent and `P_W = ∑_{j ≤ 20} x_W^j / j!` the many-white Taylor sum at the
white-term exponent `x_W = 101 z_* - A_* ℓ_c`.

The argument has two steps. First, the degree-20 partial sum of the exponential series at the
continuation logarithm `ℓ_c` exceeds `400/83`, and is at most `exp ℓ_c`; hence
`log (400/83) < ℓ_c` and, since `A_* > 0`, `(400/83)^{A_*} < exp (A_* ℓ_c)`. Second, `x_W > 0`,
so `P_W ≤ exp x_W`. Combining,
`exp (-101 z_*) (400/83)^{A_*} < exp (-101 z_* + A_* ℓ_c) = exp (-x_W) ≤ 1 / P_W`.

## Main results

* `CollatzPosDens.exp_neg_zStar_mul_rpow_Aexp_lt_log_lt_lc`: `log (400/83) < ℓ_c`.
* `CollatzPosDens.exp_neg_zStar_mul_rpow_Aexp_lt_PW_le_exp`:
  `(P_W : ℝ) ≤ exp (101 z_* - A_* ℓ_c)`.
* `CollatzPosDens.exp_neg_zStar_mul_rpow_Aexp_lt`:
  `exp (-101 z_*) (400/83)^{A_*} < 1 / P_W`.

## Implementation notes

The power `(400/83)^{A_*}` has the rational exponent `A_*`, so it is the real power
`Real.rpow` of `400/83` at the cast of `A_*` to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The continuation logarithm bounds `log (400/83)` strictly from above. -/
theorem exp_neg_zStar_mul_rpow_Aexp_lt_log_lt_lc : Real.log (400 / 83) < (lc : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hsum : ((400 / 83 : ℚ) : ℝ) <
      ((∑ j ∈ Finset.range 21, lc ^ j / (j.factorial : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast lc_expPartialSum_gt
  push_cast at hsum
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by exact_mod_cast lc_pos.le) 21)

/-- The many-white Taylor sum is a lower bound for `exp (101 z_* - A_* ℓ_c)`. -/
theorem exp_neg_zStar_mul_rpow_Aexp_lt_PW_le_exp :
    (PW : ℝ) ≤ Real.exp (101 * zStar - Aexp * lc) := by
  have h : ((101 * zStar - Aexp * lc : ℚ) : ℝ) = 101 * zStar - Aexp * lc := by
    push_cast
    rfl
  have hPW : (PW : ℝ) = ∑ j ∈ Finset.range 21,
      ((101 * zStar - Aexp * lc : ℚ) : ℝ) ^ j / (j.factorial : ℝ) := by
    rw [PW_def, Rat.cast_sum]
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  rw [hPW, ← h]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast PW_exponent_pos.le) 21

/-- **The many-white term**: `exp (-101 z_*) (400/83)^{A_*} < 1 / P_W`. -/
@[collatz_pos_dens "lem_s02_white_term"]
theorem exp_neg_zStar_mul_rpow_Aexp_lt :
    Real.exp (-(101 * zStar)) * (400 / 83 : ℝ) ^ (Aexp : ℝ) < 1 / (PW : ℝ) := by
  have hpow : (400 / 83 : ℝ) ^ (Aexp : ℝ) < Real.exp (Aexp * lc) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm (Real.log _)]
    exact Real.exp_lt_exp.mpr <| mul_lt_mul_of_pos_left
      exp_neg_zStar_mul_rpow_Aexp_lt_log_lt_lc (by exact_mod_cast Aexp_pos)
  calc Real.exp (-(101 * zStar)) * (400 / 83 : ℝ) ^ (Aexp : ℝ)
      < Real.exp (-(101 * zStar)) * Real.exp (Aexp * lc) := by gcongr
    _ = 1 / Real.exp (101 * zStar - Aexp * lc) := by
      rw [← Real.exp_add, one_div, ← Real.exp_neg]
      ring_nf
    _ ≤ 1 / (PW : ℝ) := one_div_le_one_div_of_le (by exact_mod_cast PW_pos)
        exp_neg_zStar_mul_rpow_Aexp_lt_PW_le_exp

end CollatzPosDens
