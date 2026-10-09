/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.FirstCrossing.Wb
public import CollatzPosDens.Recipe.Texp
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.UpperScale

/-!
# The height of the upper scale

For every integer `u ≥ 256` and real `R ≥ 0`, the upper scale satisfies
$$U_u(R) \le 2^{\lfloor 2u/3 \rfloor} R.$$
Writing `U_u(R) = 2^{r_u} 4^u R / (4 · 3^u)`, the bound `2^{19} ≤ 3^{12}` gives both
`2^{⌊19u/12⌋} ≤ 3^u`, so that `4^u / 3^u ≤ 2^{t(u)}`, and `B(w_u) ≥ 19 w_u / 12`. The claim
then reduces to the integer inequality `r_u + t(u) - 2 ≤ ⌊2u/3⌋`, which follows from
`w_u ≤ 3u/5` and `e_u = ⌈u/100⌉ ≥ u/100` (valid for `u ≥ 256`).

## Main results

* `CollatzPosDens.upperScale_le_two_pow_two_mul_div_three`:
  `U_u(R) ≤ 2^{⌊2u/3⌋} R` for `u ≥ 256` and `R ≥ 0`.

## Implementation notes

The bound is stated for `R ≥ 0` rather than `R > 0`. The floor `⌊2u/3⌋` is the natural-number
division `2 * u / 3`, and `t(u)` enters through `texp_add_div`, `t(u) + ⌊19u/12⌋ = 2u`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- From `2^{19} ≤ 3^{12}`: `19 j ≤ 12 B(j)`, i.e. `B(j) ≥ (19/12) j`. -/
private lemma upperScaleHeight_nineteen_mul_le_ceilLog3 (j : ℕ) :
    19 * j ≤ 12 * ceilLog3 j := by
  refine (Nat.pow_le_pow_iff_right one_lt_two).1 ?_
  calc 2 ^ (19 * j) = (2 ^ 19) ^ j := by rw [pow_mul]
    _ ≤ (3 ^ 12) ^ j := Nat.pow_le_pow_left (by norm_num) j
    _ = (3 ^ j) ^ 12 := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (2 ^ ceilLog3 j) ^ 12 := Nat.pow_le_pow_left (three_pow_le_two_pow_ceilLog3 j) 12
    _ = 2 ^ (12 * ceilLog3 j) := by rw [← pow_mul, mul_comm]

/-- The height of the upper scale: for `u ≥ 256` and `R ≥ 0`, `U_u(R) ≤ 2^{⌊2u/3⌋} R`. -/
@[collatz_pos_dens "lem_upper_scale_height"]
theorem upperScale_le_two_pow_two_mul_div_three {u : ℕ} (hu : 256 ≤ u) {R : ℝ} (hR : 0 ≤ R) :
    upperScale u R ≤ 2 ^ (2 * u / 3) * R := by
  have hB := upperScaleHeight_nineteen_mul_le_ceilLog3 (wb u)
  have hw := five_mul_wb_le u
  have he := eb_of_le hu
  have ht := texp_add_div u
  have hint : 2 * (u : ℤ) + rb u ≤ 2 + ((2 * u / 3 : ℕ) : ℤ) + ((19 * u / 12 : ℕ) : ℤ) := by
    rw [rb_def, he]
    push_cast
    omega
  have key : (4 : ℝ) ^ u * 2 ^ rb u ≤ 4 * 3 ^ u * 2 ^ (2 * u / 3) :=
    calc (4 : ℝ) ^ u * 2 ^ rb u = (2 : ℝ) ^ (2 * (u : ℤ) + rb u) := by
          rw [zpow_add₀ two_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
          norm_cast
      _ ≤ (2 : ℝ) ^ (2 + ((2 * u / 3 : ℕ) : ℤ) + ((19 * u / 12 : ℕ) : ℤ)) :=
        zpow_le_zpow_right₀ one_le_two hint
      _ = 4 * 2 ^ (19 * u / 12) * 2 ^ (2 * u / 3) := by
          rw [zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, zpow_natCast]
          norm_num
          ring
      _ ≤ 4 * 3 ^ u * 2 ^ (2 * u / 3) := by
          gcongr
          exact_mod_cast two_pow_nineteen_mul_div_twelve_le_three_pow u
  rw [upperScale_eq, div_le_iff₀ (by positivity)]
  linarith [mul_le_mul_of_nonneg_right key hR]

end CollatzPosDens
