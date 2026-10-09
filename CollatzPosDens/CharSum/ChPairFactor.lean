/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairPoint
public import CollatzPosDens.Characters.FxCharacter
public import CollatzPosDens.Characters.FxCharacterAbs

/-!
# The pair factor

Fix `n : ℕ` and a frequency `ξ` in `G_n = ResidueGroup n`. For integers `j ≥ 1`, `s` and `b`, the
*pair factor* is the normalized modulus
`Fp(j, s, b) = (1 / (b - 1)) |∑_{t=1}^{b-1} e_n(-(2^t + 3) px(j, s+b) ξ)|` when `b ≥ 2`, and
`Fp(j, s, b) = 1` when `b ≤ 1`, where `px` is the pair point and `e_n` the standard additive
character of `G_n`. It is a real number in `[0, 1]`: the average of `b - 1` unit complex numbers
has modulus at most `1`.

## Main definitions

* `CollatzPosDens.chPairFactor n ξ j s b`: the pair factor `Fp(j, s, b)`.

## Main results

* `CollatzPosDens.chPairFactor_of_two_le`, `CollatzPosDens.chPairFactor_of_le_one`:
  the two cases of the definition.
* `CollatzPosDens.chPairFactor_nonneg`, `CollatzPosDens.chPairFactor_le_one`:
  `0 ≤ Fp(j, s, b) ≤ 1`.

## Implementation notes

The modulus exponent `n` and the frequency `ξ` are explicit arguments. The index `j` is a natural
number, following `chPairPoint`; the definition is meaningful for `j ≥ 1`. The summation index `t`
runs over the natural numbers `1 ≤ t ≤ b - 1`, written `Finset.Icc 1 (b.toNat - 1)`, and the power
`2^t` is taken in `G_n`. The absolute value of the complex number is its norm, so the factor is
real-valued.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The pair factor `Fp(j, s, b)`: equal to
`(1 / (b - 1)) ‖∑_{t=1}^{b-1} e_n(-(2^t + 3) px(j, s+b) ξ)‖` if `b ≥ 2`, and to `1` otherwise. -/
@[collatz_pos_dens "def_ch_pair_factor"]
noncomputable def chPairFactor (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s b : ℤ) : ℝ :=
  if 2 ≤ b then
    1 / ((b : ℝ) - 1) * ‖∑ t ∈ Finset.Icc 1 (b.toNat - 1),
      fxChar n (-((2 : ResidueGroup n) ^ t + 3) * chPairPoint n j (s + b) * ξ)‖
  else 1

/-- The pair factor for `b ≥ 2`. -/
theorem chPairFactor_of_two_le (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) {b : ℤ}
    (hb : 2 ≤ b) :
    chPairFactor n ξ j s b = 1 / ((b : ℝ) - 1) * ‖∑ t ∈ Finset.Icc 1 (b.toNat - 1),
      fxChar n (-((2 : ResidueGroup n) ^ t + 3) * chPairPoint n j (s + b) * ξ)‖ := by
  simp [chPairFactor, hb]

/-- The pair factor for `b ≤ 1` is `1`. -/
theorem chPairFactor_of_le_one (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) {b : ℤ}
    (hb : b ≤ 1) : chPairFactor n ξ j s b = 1 := by
  simp [chPairFactor, show ¬ 2 ≤ b by omega]

/-- The pair factor is nonnegative. -/
theorem chPairFactor_nonneg (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s b : ℤ) :
    0 ≤ chPairFactor n ξ j s b := by
  unfold chPairFactor
  split_ifs with hb
  · have : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    positivity
  · exact zero_le_one

/-- The pair factor is at most `1`. -/
theorem chPairFactor_le_one (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s b : ℤ) :
    chPairFactor n ξ j s b ≤ 1 := by
  unfold chPairFactor
  split_ifs with hb
  · have hpos : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (2 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
    have hcard : ((Finset.Icc 1 (b.toNat - 1)).card : ℝ) = (b : ℝ) - 1 := by
      have hc : (Finset.Icc 1 (b.toNat - 1)).card = b.toNat - 1 := by
        rw [Nat.card_Icc]; omega
      have hk : (((b.toNat - 1 : ℕ) : ℤ) : ℝ) = ((b - 1 : ℤ) : ℝ) := by
        congr 1; omega
      rw [hc]; push_cast at hk; exact hk
    have hle : ‖∑ t ∈ Finset.Icc 1 (b.toNat - 1),
        fxChar n (-((2 : ResidueGroup n) ^ t + 3) * chPairPoint n j (s + b) * ξ)‖ ≤
        (b : ℝ) - 1 := by
      refine (norm_sum_le _ _).trans ?_
      simp only [fxChar_norm_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact hcard.le
    rw [div_mul_eq_mul_div, one_mul, div_le_one hpos]
    exact hle
  · exact le_rfl

end CollatzPosDens
