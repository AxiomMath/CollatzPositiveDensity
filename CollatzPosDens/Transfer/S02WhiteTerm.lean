/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Lc
public import CollatzPosDens.Transfer.S02PW
public import CollatzPosDens.Transfer.S02Xwc
public import CollatzPosDens.Transfer.S02Z
public import CollatzPosDens.Transfer.Tstar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The many-white term

For every Fourier index `ι` we prove `exp (-z_* T_*(ι)) (400/83)^{A_*(ι)} < 1 / P_W(ι)`, where
`z_*` is the white Fourier penalty, `T_*(ι)` the low-count threshold, `A_*(ι)` the decay exponent
and `P_W(ι) = ∑_{j ≤ 20} x_W(ι)^j / j!` the many-white Taylor sum at the many-white exponent
`x_W(ι) = z_* T_*(ι) - A_*(ι) ℓ_c`.

The argument has two steps. First, the degree-20 partial sum of the exponential series at the
continuation logarithm `ℓ_c` exceeds `400/83`, and is at most `exp ℓ_c`; hence
`log (400/83) < ℓ_c` and, since `A_*(ι) > 0`, `(400/83)^{A_*(ι)} < exp (A_*(ι) ℓ_c)`. Second,
`x_W(ι) > 0` (explicitly `x_W(o) = (133/3125)·192 - (21193/10000) ℓ_c = 4838645241/10⁹` and
`x_W(b) = (133/3125)·168 - (17/10) ℓ_c = 4476609/10⁶`, with `ℓ_c = 157263/100000`), so
`P_W(ι) ≤ exp x_W(ι)`. Combining,
`exp (-z_* T_*(ι)) (400/83)^{A_*(ι)} < exp (-z_* T_*(ι) + A_*(ι) ℓ_c) = exp (-x_W(ι))
≤ 1 / P_W(ι)`.

## Main results

* `CollatzPosDens.log_400_div_83_lt_lc`: `log (400/83) < ℓ_c`.
* `CollatzPosDens.PW_le_exp_xW`: `(P_W(ι) : ℝ) ≤ exp x_W(ι)`.
* `CollatzPosDens.exp_neg_zStar_mul_rpow_Aexp_lt`:
  `exp (-z_* T_*(ι)) (400/83)^{A_*(ι)} < 1 / P_W(ι)`.

## Implementation notes

The power `(400/83)^{A_*(ι)}` has the rational exponent `A_*(ι)`, so it is the real power
`Real.rpow` of `400/83` at the cast of `A_*(ι)` to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The continuation logarithm bounds `log (400/83)` strictly from above. -/
theorem log_400_div_83_lt_lc : Real.log (400 / 83) < (lc : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have hsum : ((400 / 83 : ℚ) : ℝ) <
      ((∑ j ∈ Finset.range 21, lc ^ j / (j.factorial : ℚ) : ℚ) : ℝ) :=
    mod_cast lc_expPartialSum_gt
  push_cast at hsum
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (mod_cast lc_pos.le) 21)

/-- The many-white Taylor sum is a lower bound for `exp x_W(ι)`. -/
theorem PW_le_exp_xW (ι : FIndex) : (PW ι : ℝ) ≤ Real.exp (xW ι) := by
  have hPW : (PW ι : ℝ) = ∑ j ∈ Finset.range 21, (xW ι : ℝ) ^ j / (j.factorial : ℝ) := by
    simp only [PW_def, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  rw [hPW]
  exact Real.sum_le_exp_of_nonneg (mod_cast (xW_pos ι).le) 21

/-- **The many-white term**: for every Fourier index `ι`,
`exp (-z_* T_*(ι)) (400/83)^{A_*(ι)} < 1 / P_W(ι)`. -/
@[collatz_pos_dens "lem_s02_white_term"]
theorem exp_neg_zStar_mul_rpow_Aexp_lt (ι : FIndex) :
    Real.exp (-((zStar : ℝ) * tStar ι)) * (400 / 83 : ℝ) ^ (Aexp ι : ℝ) < 1 / (PW ι : ℝ) := by
  have hpow : (400 / 83 : ℝ) ^ (Aexp ι : ℝ) < Real.exp (Aexp ι * lc) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm (Real.log _)]
    exact Real.exp_lt_exp.mpr <|
      mul_lt_mul_of_pos_left log_400_div_83_lt_lc (mod_cast Aexp_pos ι)
  have hxW : ((xW ι : ℚ) : ℝ) = (zStar : ℝ) * tStar ι - Aexp ι * lc := by
    simp only [xW]
    push_cast
    rfl
  calc Real.exp (-((zStar : ℝ) * tStar ι)) * (400 / 83 : ℝ) ^ (Aexp ι : ℝ)
      < Real.exp (-((zStar : ℝ) * tStar ι)) * Real.exp (Aexp ι * lc) := by gcongr
    _ = 1 / Real.exp (xW ι) := by
      rw [hxW, ← Real.exp_add, one_div, ← Real.exp_neg]
      ring_nf
    _ ≤ 1 / (PW ι : ℝ) := one_div_le_one_div_of_le (mod_cast PW_pos ι) (PW_le_exp_xW ι)

end CollatzPosDens
