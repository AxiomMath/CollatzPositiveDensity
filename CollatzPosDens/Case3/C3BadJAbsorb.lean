/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.Dbad
public import CollatzPosDens.Monotone.MoLogSqrt
public import CollatzPosDens.Transfer.Exp9

/-!
# Absorption of the outer horizontal tail

With `A = Aexp`, `P = pStar` and `Dbad = (2^53 A)^2 + 2^53 (P + 65)`, for every real
`m ≥ Dbad`,
$$m^{A}\bigl(2^{55} + e^{P/2}\bigr) e^{-m/2^{51}} < \tfrac1{8000}.$$
The first summand of `Dbad` gives `√m ≥ 2^53 A`, hence `A log m ≤ A √m ≤ m / 2^53` (using
`log x ≤ √x`); the second gives `P + 56 ≤ m / 2^53 - 9`. Since `2 ≤ e`,
`2^55 + e^{P/2} ≤ e^{P + 56}`, so the logarithm of the left side is at most
`-9 - 2m/2^53 ≤ -9`, and `e^{-9} < 1/8000`.

## Main results

* `CollatzPosDens.c3_badJ_absorb_of_le`: the inequality for arbitrary reals `A, P ≥ 0` in
  place of `Aexp, pStar`, under `(2^53 A)^2 + 2^53 (P + 65) ≤ m`.
* `CollatzPosDens.c3_badJ_absorb`: the inequality for `m ≥ Dbad`.

## Implementation notes

The power `m^A` is the real power `Real.rpow` with exponent the cast of `Aexp ∈ ℚ`. The
argument uses neither the value of `Aexp` nor that of `pStar`, only their nonnegativity, so it
is first proved for arbitrary nonnegative reals `A` and `P`.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `A, P ≥ 0` and `(2^53 A)^2 + 2^53 (P + 65) ≤ m`, then
`m ^ A (2 ^ 55 + e ^ (P / 2)) e ^ (-m / 2 ^ 51) < 1 / 8000`. -/
theorem c3_badJ_absorb_of_le {A P m : ℝ} (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hm : (2 ^ 53 * A) ^ 2 + 2 ^ 53 * (P + 65) ≤ m) :
    m ^ A * (2 ^ 55 + Real.exp (P / 2)) * Real.exp (-m / 2 ^ 51) < 1 / 8000 := by
  have hsq : 0 ≤ (2 ^ 53 * A) ^ 2 := sq_nonneg _
  have hm0 : 0 < m := by nlinarith
  have hs : 2 ^ 53 * A ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by linarith)
  have hlog : A * Real.log m ≤ m / 2 ^ 53 := by
    have h1 : A * Real.log m ≤ A * Real.sqrt m :=
      mul_le_mul_of_nonneg_left (log_le_sqrt hm0.le) hA
    have h2 : (2 ^ 53 * A) * Real.sqrt m ≤ Real.sqrt m * Real.sqrt m :=
      mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg m)
    rw [Real.mul_self_sqrt hm0.le] at h2
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hpow : m ^ A ≤ Real.exp (m / 2 ^ 53) := by
    rw [Real.rpow_def_of_pos hm0, mul_comm]
    exact Real.exp_le_exp.2 hlog
  have h55 : (2 : ℝ) ^ 55 ≤ Real.exp (P + 55) := by
    calc (2 : ℝ) ^ 55 ≤ Real.exp 1 ^ 55 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
      _ = Real.exp 55 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp (P + 55) := Real.exp_le_exp.2 (by linarith)
  have h2e : 2 * Real.exp (P + 55) ≤ Real.exp (P + 56) := by
    rw [show P + 56 = 1 + (P + 55) by ring, Real.exp_add 1 (P + 55)]
    gcongr
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : 2 ^ 55 + Real.exp (P / 2) ≤ Real.exp (P + 56) := by
    linarith [Real.exp_le_exp.2 (show P / 2 ≤ P + 55 by linarith)]
  have hPm : P + 56 ≤ m / 2 ^ 53 - 9 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    nlinarith
  calc m ^ A * (2 ^ 55 + Real.exp (P / 2)) * Real.exp (-m / 2 ^ 51)
      ≤ Real.exp (m / 2 ^ 53) * Real.exp (P + 56) * Real.exp (-m / 2 ^ 51) := by
        gcongr
    _ = Real.exp (m / 2 ^ 53 + (P + 56) + -m / 2 ^ 51) := by
        rw [Real.exp_add (m / 2 ^ 53 + (P + 56)), Real.exp_add (m / 2 ^ 53)]
    _ ≤ Real.exp (-9) := Real.exp_le_exp.2 (by linarith)
    _ < 1 / 8000 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
        simpa using exp_nine_gt

/-- For every real `m ≥ Dbad`,
`m ^ Aexp (2 ^ 55 + e ^ (pStar / 2)) e ^ (-m / 2 ^ 51) < 1 / 8000`. -/
@[collatz_pos_dens "lem_c3_badJ_absorb"]
theorem c3_badJ_absorb {m : ℝ} (hm : (Dbad : ℝ) ≤ m) :
    m ^ (Aexp : ℝ) * (2 ^ 55 + Real.exp ((pStar : ℝ) / 2)) * Real.exp (-m / 2 ^ 51) <
      1 / 8000 :=
  c3_badJ_absorb_of_le (by exact_mod_cast Aexp_pos.le) (Nat.cast_nonneg _)
    (by rwa [cast_Dbad] at hm)

end CollatzPosDens
