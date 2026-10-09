/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSignedFrac
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkThetaResidue
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.CharSum.ChPairPoint
public import CollatzPosDens.Transfer.DyadicReduction
public import CollatzPosDens.Characters.FxCharacterAbs
public import CollatzPosDens.Characters.FxCharacterHom
public import CollatzPosDens.Characters.FxCharacterInt

/-!
# The pair factor through the angle

Fix `n : ℕ` and `ξ ∈ G_n`. For `j ≥ 1`, `s ∈ ℤ` and `b ≥ 2`, the pair factor is expressed through
the angle `ϑ_{n,ξ}(j, s + b)`:
`Fp(j, s, b) = (1 / (b - 1)) |∑_{t=1}^{b-1} exp(-2πi (2^{t-1} - 1) ϑ_{n,ξ}(j, s + b))|`.

Writing `x = px(j, s + b)` and `k_t = 2^{t-1} - 1`, one has `2^t + 3 = 5 + 2 k_t`, so each term
`e_n(-(2^t + 3) x ξ)` factors as `e_n(-5 x ξ) e_n(-k_t · 2 x ξ)`. Since reduction modulo `3^n` is a
ring homomorphism, `2 x ξ` is the angle residue `r_{n,ξ}(j, s + b)`, and for every integer `k`,
`e_n(-k r) = exp(-2πi k sfr(r))`. The common factor `e_n(-5 x ξ)` has modulus one.

## Main results

* `CollatzPosDens.chPairFactor_eq_norm_sum_exp_bkTheta`: the formula for `Fp(j, s, b)`.

## Implementation notes

The hypothesis `j ≥ 1` is not needed: the index `j` is a natural number, and both the pair point
and the angle residue use the truncated exponent `2(j - 1)`, which agree at `j = 0`. The
summation index `t` ranges over `Finset.Icc 1 (b.toNat - 1)`, as in `chPairFactor`, and
`2^{t-1} - 1` is computed in `ℂ`; on this range it is the natural number `k_t`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- For `k ∈ ℤ` and `z ∈ G_n`, `e_n(-k z) = exp(-2πi k sfr(z))`. -/
private theorem fxChar_neg_intCast_mul_eq_exp_sfr (n : ℕ) (k : ℤ) (z : ResidueGroup n) :
    fxChar n (-(k : ResidueGroup n) * z) = exp (-2 * π * I * k * (sfr z : ℂ)) := by
  have hz : ((z.valMinAbs : ℤ) : ResidueGroup n) = z := ZMod.coe_valMinAbs z
  have hx : -(k : ResidueGroup n) * z = ((-k * z.valMinAbs : ℤ) : ResidueGroup n) := by
    rw [Int.cast_mul, Int.cast_neg, hz]
  rw [hx, fxChar_eq_exp_of_intModEq n _ (-k * z.valMinAbs)
    (by rw [ZMod.val_intCast]; exact (Int.mod_modEq _ _).symm), sfr_def]
  congr 1
  push_cast
  have h3 : (3 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- `2 px(j, l) ξ = r_{n,ξ}(j, l)`: twice the pair point times `ξ` is the angle residue. -/
private theorem two_mul_chPairPoint_mul (n j : ℕ) (l : ℤ) (ξ : ResidueGroup n) :
    2 * chPairPoint n j l * ξ = bkThetaResidue n ξ ((j : ℤ), l) := by
  rw [chPairPoint_eq, bkThetaResidue_eq]
  have hu : (isUnit_two_residueGroup n).unit = ZMod.unitOfCoprime 2 (coprime_two_three_pow n) :=
    Units.ext (by simp)
  have he : (2 * (bkJ ((j : ℤ), l) - 1)).toNat = 2 * (j - 1) := by simp only [bkJ]; omega
  have hl : bkL ((j : ℤ), l) = l := rfl
  rw [hu, he, hl, sub_eq_add_neg, add_comm, zpow_add, zpow_one, Units.val_mul]
  have h2 : ((ZMod.unitOfCoprime 2 (coprime_two_three_pow n) : (ZMod (3 ^ n))ˣ) :
      ResidueGroup n) = 2 := by simp
  rw [h2]
  ring

/-- The pair factor through the angle: for `b ≥ 2`,
`Fp(j, s, b) = (1 / (b - 1)) ‖∑_{t=1}^{b-1} exp(-2πi (2^{t-1} - 1) ϑ_{n,ξ}(j, s + b))‖`. -/
@[collatz_pos_dens "lem_ch_fp_formula"]
theorem chPairFactor_eq_norm_sum_exp_bkTheta (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ)
    {b : ℤ} (hb : 2 ≤ b) :
    chPairFactor n ξ j s b = 1 / ((b : ℝ) - 1) * ‖∑ t ∈ Finset.Icc 1 (b.toNat - 1),
      exp (-2 * π * I * ((2 : ℂ) ^ (t - 1) - 1) * (bkTheta n ξ ((j : ℤ), s + b) : ℂ))‖ := by
  rw [chPairFactor_of_two_le n ξ j s hb]
  congr 1
  set x := chPairPoint n j (s + b)
  have hterm : ∀ t ∈ Finset.Icc 1 (b.toNat - 1),
      fxChar n (-((2 : ResidueGroup n) ^ t + 3) * x * ξ) =
        fxChar n (-5 * x * ξ) *
          exp (-2 * π * I * ((2 : ℂ) ^ (t - 1) - 1) * (bkTheta n ξ ((j : ℤ), s + b) : ℂ)) := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
    have hsplit : -((2 : ResidueGroup n) ^ (m + 1) + 3) * x * ξ =
        -5 * x * ξ + -(((2 ^ m - 1 : ℕ) : ℤ) : ResidueGroup n) * (2 * x * ξ) := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      push_cast [h1]
      ring
    rw [hsplit, fxChar_add_eq_mul, two_mul_chPairPoint_mul, fxChar_neg_intCast_mul_eq_exp_sfr,
      ← bkTheta_def]
    congr 3
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    simp [h1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, norm_mul, fxChar_norm_eq_one, one_mul]

end CollatzPosDens
