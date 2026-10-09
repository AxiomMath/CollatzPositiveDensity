/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSeWeight
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkResidueShift
public import CollatzPosDens.BlackSet.BkSfrRep

/-!
# The angle scales exactly by `exp se` while it stays small

For points `a, q ∈ 𝒫` with `j(a) ≤ j(q)`, `l(q) ≤ l(a)` and `e^{se(a,q)} |ϑ(a)| < 1/2`,
the angle of `q` satisfies `|ϑ(q)| = e^{se(a,q)} |ϑ(a)|`. Indeed `h = e^{se(a,q)}` is the
positive integer `9^{j(q)-j(a)} 2^{l(a)-l(q)}`, the integer `h · 3^n ϑ(a)` represents
`h · r(a) = r(q)`, and it is small enough to be the signed representative used to define `ϑ(q)`.

## Main results

* `CollatzPosDens.abs_bkTheta_eq_exp_bkSe_mul`: `|ϑ(q)| = e^{se(a,q)} |ϑ(a)|`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `a, q ∈ 𝒫` with `j(a) ≤ j(q)`, `l(q) ≤ l(a)` and `e^{se(a,q)} |ϑ(a)| < 1/2`, one has
`|ϑ(q)| = e^{se(a,q)} |ϑ(a)|`. -/
@[collatz_pos_dens "lem_bk_se_exact"]
theorem abs_bkTheta_eq_exp_bkSe_mul (n : ℕ) (ξ : ResidueGroup n) {a q : ℤ × ℤ}
    (ha : a ∈ bkPoints) (hq : q ∈ bkPoints) (hj : bkJ a ≤ bkJ q) (hl : bkL q ≤ bkL a)
    (hsmall : Real.exp (bkSe a q) * |bkTheta n ξ a| < 1 / 2) :
    |bkTheta n ξ q| = Real.exp (bkSe a q) * |bkTheta n ξ a| := by
  set h : ℕ := 9 ^ (bkJ q - bkJ a).toNat * 2 ^ (bkL a - bkL q).toNat with hh
  have hexp : Real.exp (bkSe a q) = (h : ℝ) := exp_bkSe_eq_natCast hj hl
  have hN : (0 : ℝ) < ((3 ^ n : ℕ) : ℝ) := by positivity
  set v : ℤ := (bkThetaResidue n ξ a).valMinAbs with hv
  have htheta : bkTheta n ξ a = (v : ℝ) / ((3 ^ n : ℕ) : ℝ) := by
    rw [bkTheta_def, sfr_def]
  have hrep : (((h : ℤ) * v : ℤ) : ZMod (3 ^ n)) = bkThetaResidue n ξ q := by
    rw [bkThetaResidue_shift n ξ ha hq hj hl, ← hh]
    push_cast
    rw [hv, ZMod.coe_valMinAbs]
  rw [hexp, htheta, abs_div, abs_of_pos hN] at hsmall ⊢
  have hhabs : |(((h : ℤ) * v : ℤ) : ℝ)| < ((3 ^ n : ℕ) : ℝ) / 2 := by
    push_cast
    rw [abs_mul, Nat.abs_cast]
    rw [← mul_div_assoc, div_lt_iff₀ hN] at hsmall
    push_cast at hsmall
    linarith
  rw [bkTheta_def, sfr_eq_of_abs_lt hrep hhabs, abs_div, abs_of_pos hN]
  push_cast
  rw [abs_mul, Nat.abs_cast, mul_div_assoc]

end CollatzPosDens
