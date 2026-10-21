/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Dbad
public import CollatzPosDens.Transfer.S02Exp9

/-!
# Absorption of the outer horizontal tail

For every Fourier index `ι ∈ {o, b}` and every real `m ≥ D_bad(ι) = 2^21 (P_*(ι) + 64)`, so that
also `m ≥ 2^43` (as `D_bad(ι) ≥ 2^43`),
$$m^{A_*(ι)}\bigl(6 e^{-m/2^{36}} + e^{P_*(ι)/2 - m/3200000}\bigr) < \tfrac1{8000}.$$
Since `log 2 < 1` and `log x ≤ x - 1`, writing `m = 2^43 x` gives `log m < 42 + m / 2^43`, so
`A log m ≤ (5/2) log m ≤ m / 2^36 - 13` for `A ≤ 5/2` and `m ≥ 2^43`. The logarithm of the first
term is then at most `log 6 - 13 < -10`, as `e^3 > 6`; the bound `m ≥ 2^21 (P_* + 64)` gives
`P_*/2 ≤ m / 2^22 - 32`, and as `1/2^36 + 1/2^22 < 1/3200000` the logarithm of the second term is
below `-32`. Both terms are below `e^{-10}`, and `2 e^{-10} < 1/8000` since
`e^{10} = e^9 e > 8000 · 2`.

## Main results

* `CollatzPosDens.c3_badJ_absorb_of_le`: the inequality for arbitrary reals `A ≤ 5/2` and
  `P` in place of `A_*(ι)` and `P_*(ι)`, under `2^43 ≤ m` and `2^21 (P + 64) ≤ m`.
* `CollatzPosDens.c3_badJ_absorb`: the inequality for `m ≥ D_bad(ι)`.

## Implementation notes

The power `m^{A_*(ι)}` is the real power `Real.rpow` with exponent the cast of `A_*(ι) ∈ ℚ`. The
argument uses only `A_*(ι) ≤ 5/2` and not the value of `P_*(ι)`, so it is first proved for
arbitrary reals `A` and `P`; positivity of `A` is not needed, since `log m ≥ 0`.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `A ≤ 5/2`, `2^43 ≤ m` and `2^21 (P + 64) ≤ m`, then
`m ^ A (6 e ^ (-m / 2 ^ 36) + e ^ (P / 2 - m / 3200000)) < 1 / 8000`. -/
theorem c3_badJ_absorb_of_le {A P m : ℝ} (hA : A ≤ 5 / 2) (hm : 2 ^ 43 ≤ m)
    (hPm : 2 ^ 21 * (P + 64) ≤ m) :
    m ^ A * (6 * Real.exp (-m / 2 ^ 36) + Real.exp (P / 2 - m / 3200000)) < 1 / 8000 := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogm : Real.log m < 42 + m / 2 ^ 43 := by
    have hx : 0 < m / 2 ^ 43 := by positivity
    have hsplit : Real.log m = 43 * Real.log 2 + Real.log (m / 2 ^ 43) := by
      rw [Real.log_div hm0.ne' (by norm_num), Real.log_pow]
      push_cast
      ring
    have h1 := Real.log_le_sub_one_of_pos hx
    have h2 : Real.log 2 < 1 := (Real.log_lt_iff_lt_exp two_pos).2 (by
      linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)])
    linarith
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hlog : A * Real.log m ≤ m / 2 ^ 36 - 13 := by
    have : A * Real.log m ≤ 5 / 2 * Real.log m := mul_le_mul_of_nonneg_right hA hlog0
    linarith
  have hpow : m ^ A ≤ Real.exp (m / 2 ^ 36 - 13) := by
    rw [Real.rpow_def_of_pos hm0, mul_comm]
    exact Real.exp_le_exp.2 hlog
  have h6 : (6 : ℝ) ≤ Real.exp 3 := by
    nlinarith [Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
  have hpow0 : 0 ≤ m ^ A := Real.rpow_nonneg hm0.le A
  have hT1 : m ^ A * (6 * Real.exp (-m / 2 ^ 36)) ≤ Real.exp (-10) := by
    calc m ^ A * (6 * Real.exp (-m / 2 ^ 36))
        ≤ Real.exp (m / 2 ^ 36 - 13) * (Real.exp 3 * Real.exp (-m / 2 ^ 36)) := by gcongr
      _ = Real.exp (m / 2 ^ 36 - 13 + (3 + -m / 2 ^ 36)) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-10) := Real.exp_le_exp.2 (by linarith)
  have hT2 : m ^ A * Real.exp (P / 2 - m / 3200000) ≤ Real.exp (-10) := by
    calc m ^ A * Real.exp (P / 2 - m / 3200000)
        ≤ Real.exp (m / 2 ^ 36 - 13) * Real.exp (P / 2 - m / 3200000) := by gcongr
      _ = Real.exp (m / 2 ^ 36 - 13 + (P / 2 - m / 3200000)) := by rw [Real.exp_add]
      _ ≤ Real.exp (-10) := Real.exp_le_exp.2 (by linarith)
  have h10 : (16000 : ℝ) < Real.exp 10 := by
    rw [show (10 : ℝ) = 9 + 1 by norm_num, Real.exp_add]
    nlinarith [exp_nine_gt]
  have hfin : 2 * Real.exp (-10) < 1 / 8000 := by
    rw [Real.exp_neg]
    have := Real.exp_pos 10
    rw [← div_eq_mul_inv, div_lt_div_iff₀ this (by norm_num)]
    linarith
  rw [mul_add]
  linarith

/-- For every Fourier index `ι` and every real `m ≥ D_bad(ι)`,
`m ^ A_*(ι) (6 e ^ (-m / 2 ^ 36) + e ^ (P_*(ι) / 2 - m / 3200000)) < 1 / 8000`. -/
@[collatz_pos_dens "lem_c3_badJ_absorb"]
theorem c3_badJ_absorb (ι : FIndex) {m : ℝ} (hm : (Dbad ι : ℝ) ≤ m) :
    m ^ (Aexp ι : ℝ) *
        (6 * Real.exp (-m / 2 ^ 36) + Real.exp ((pStar ι : ℝ) / 2 - m / 3200000)) <
      1 / 8000 := by
  have h43 : (2 : ℝ) ^ 43 ≤ m := le_trans (by exact_mod_cast two_pow_43_le_Dbad ι) hm
  rw [cast_Dbad] at hm
  refine c3_badJ_absorb_of_le ?_ h43 hm
  cases ι <;> norm_num [Aexp_cast_o, Aexp_cast_b]

end CollatzPosDens
