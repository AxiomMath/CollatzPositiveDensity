/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Transfer.S02Amix

/-!
# The clipping base of the count

For an integer `t ≥ 1`, the *clipping base of the count* is the real number
$$x_{\mathrm{ct}}(t) = \bigl(2^{420}\, t\, (1 + \log t)\bigr)^{1/a_{\mathrm{mx}}(\mathrm o)},$$
a positive real power, where `log` is the natural logarithm and `a_mx(o) = 18693/10000` is the
profile exponent `CollatzPosDens.amix` at the original index.

## Main definitions

* `CollatzPosDens.countX t`: the clipping base `x_ct(t)`.

## Main results

* `CollatzPosDens.countX_rpow_amix`: `x_ct(t)^{a_mx(o)} = 2^{420} t (1 + log t)`.
* `CollatzPosDens.one_le_countX`: `1 ≤ x_ct(t)` for `t ≥ 1`.
* `CollatzPosDens.log_countX`:
  `log x_ct(t) = (420 log 2 + log t + log (1 + log t)) / a_mx(o)` for `t ≥ 1`.

## Implementation notes

The definition is made for every `t ∈ ℕ`; since `log 0 = 0`, its base `2^{420} t (1 + log t)` is
nonnegative for every natural `t`.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping base of the count, `x_ct(t) = (2^{420} t (1 + log t))^{1/a_mx(o)} ∈ ℝ`, a real
power, with `log` the natural logarithm. -/
@[collatz_pos_dens "def_s06_count_x"]
noncomputable def countX (t : ℕ) : ℝ :=
  (2 ^ 420 * (t : ℝ) * (1 + Real.log t)) ^ (1 / (amix .o : ℝ))

/-- Unfolding lemma for `countX`. -/
theorem countX_def (t : ℕ) :
    countX t = (2 ^ 420 * (t : ℝ) * (1 + Real.log t)) ^ (1 / (amix .o : ℝ)) :=
  rfl

/-- The base `2^{420} t (1 + log t)` of the clipping base is nonnegative. -/
theorem countX_base_nonneg (t : ℕ) : 0 ≤ 2 ^ 420 * (t : ℝ) * (1 + Real.log t) := by
  have := Real.log_natCast_nonneg t
  positivity

/-- The base `2^{420} t (1 + log t)` of the clipping base is at least `2^{420}` for `t ≥ 1`. -/
theorem two_pow_le_countX_base {t : ℕ} (ht : 1 ≤ t) :
    (2 : ℝ) ^ 420 ≤ 2 ^ 420 * (t : ℝ) * (1 + Real.log t) := by
  have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h2 := Real.log_natCast_nonneg t
  have h3 : (1 : ℝ) ≤ t * (1 + Real.log t) := by nlinarith
  rw [mul_assoc]
  exact le_mul_of_one_le_right (by positivity) h3

/-- The clipping base is nonnegative. -/
theorem countX_nonneg (t : ℕ) : 0 ≤ countX t :=
  Real.rpow_nonneg (countX_base_nonneg t) _

/-- The clipping base raised to the profile exponent: `x_ct(t)^{a_mx(o)} = 2^{420} t (1 + log t)`.
-/
theorem countX_rpow_amix (t : ℕ) :
    countX t ^ (amix .o : ℝ) = 2 ^ 420 * (t : ℝ) * (1 + Real.log t) := by
  rw [countX_def, one_div]
  exact Real.rpow_inv_rpow (countX_base_nonneg t) (by rw [amix_cast_o]; norm_num)

/-- The clipping base is at least `1` for `t ≥ 1`. -/
theorem one_le_countX {t : ℕ} (ht : 1 ≤ t) : 1 ≤ countX t := by
  rw [countX_def]
  refine Real.one_le_rpow ((one_le_pow₀ (by norm_num)).trans (two_pow_le_countX_base ht)) ?_
  rw [amix_cast_o]; norm_num

/-- The clipping base is positive for `t ≥ 1`. -/
theorem countX_pos {t : ℕ} (ht : 1 ≤ t) : 0 < countX t :=
  zero_lt_one.trans_le (one_le_countX ht)

/-- The logarithm of the clipping base, for `t ≥ 1`:
`log x_ct(t) = (420 log 2 + log t + log (1 + log t)) / a_mx(o)`. -/
theorem log_countX {t : ℕ} (ht : 1 ≤ t) :
    Real.log (countX t) =
      (420 * Real.log 2 + Real.log t + Real.log (1 + Real.log t)) / (amix .o : ℝ) := by
  have h1 : (0 : ℝ) < t := by exact_mod_cast ht
  have h2 : 0 < 1 + Real.log t := by linarith [Real.log_natCast_nonneg t]
  rw [countX_def, Real.log_rpow (by positivity), Real.log_mul (by positivity) h2.ne',
    Real.log_mul (by positivity) h1.ne', Real.log_pow]
  push_cast
  ring

end CollatzPosDens
