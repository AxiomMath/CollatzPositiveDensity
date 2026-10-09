/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Recipe.PhH0Large
public import CollatzPosDens.Transfer.Log2C

/-!
# A lower bound for the modulus exponent

The fixed modulus exponent `m = ⌊(2^39 𝓜 C)^{8/9}⌋₊ + 1` satisfies `m > 2^131072`.

Indeed the mixing coefficient satisfies `C ≥ 1` (its binary logarithm is positive), so
$$m > (2^{39}\mathcal{M}C)^{8/9} \ge \mathcal{M}^{8/9} = 2^{(8/9)\log_2\mathcal{M}}
  > 2^{(8/9)10^{12}} > 2^{131072},$$
using `log₂ 𝓜 > 10^12`.

## Main results

* `CollatzPosDens.two_pow_lt_modulusExponent`: `2 ^ 131072 < m`.

## Implementation notes

The inequality is stated in `ℕ`, where `m` lives.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The modulus exponent `modulusExponent` exceeds `2 ^ 131072`. -/
@[collatz_pos_dens "lem_m_gate"]
theorem two_pow_lt_modulusExponent : 2 ^ 131072 < modulusExponent := by
  have hM : (0 : ℝ) < seedBound := by exact_mod_cast seedBound_pos
  have hC : (1 : ℝ) ≤ mixingConst := one_le_mixingConst
  have hL := logb_two_seedBound_gt
  have h1 : (seedBound : ℝ) ^ (8 / 9 : ℝ) ≤
      ((2 : ℝ) ^ 39 * seedBound * mixingConst) ^ (8 / 9 : ℝ) := by
    apply rpow_le_rpow hM.le _ (by norm_num)
    have : (seedBound : ℝ) ≤ (2 : ℝ) ^ 39 * seedBound := by
      nlinarith [show (1 : ℝ) ≤ 2 ^ 39 by norm_num]
    calc (seedBound : ℝ) ≤ (2 : ℝ) ^ 39 * seedBound := this
      _ ≤ (2 : ℝ) ^ 39 * seedBound * mixingConst := by
        nlinarith [show (0 : ℝ) < 2 ^ 39 by norm_num]
  have h2 : (2 : ℝ) ^ (131072 : ℝ) < (seedBound : ℝ) ^ (8 / 9 : ℝ) := by
    rw [← rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hM, ← rpow_mul (by norm_num)]
    exact rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h3 := lt_modulusExponent
  have h4 : (2 : ℝ) ^ (131072 : ℕ) < modulusExponent := by
    rw [← rpow_natCast, Nat.cast_ofNat]
    linarith
  exact_mod_cast h4

end CollatzPosDens
