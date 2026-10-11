/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Tower
public import CollatzPosDens.Recipe.QstarGe
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.PhConductor
public import CollatzPosDens.Recipe.PhEndpoint

/-!
# The seed allowance at `s = 1` is below the tower

The seed allowance at endpoint `1` satisfies `2^33 𝓜(1)^4 < tow_3(140214)`.

Write `q = q_*` for the conductor. Since `q ≥ 9 N_* ≥ 3`, and `log₂ q + 1 < 16 + N_* δ <
140213 + 9/16`, the exact inequality `3^16 > 2^25` (that is, `log₂ (3/2) > 9/16`) gives
`log₂ q < 140211 + log₂ 3`, i.e. `q < 3 · 2^140211`. Since `𝓜(1) = 2^{38 + 4·3^q}`, we have
`2^33 𝓜(1)^4 = 2^Y` with `Y = 185 + 16·3^q < 32·3^q < 2^{5 + 2q}`, and
`5 + 2q < 8 · 2^140211 = 2^140214`. Monotonicity of `x ↦ 2^x` then gives the claim.

## Main results

* `CollatzPosDens.tower_three`: `tow_3(t) = 2^2^2^t`.
* `CollatzPosDens.conductor_lt_three_mul_two_pow`: `q_* < 3 · 2^140211`.
* `CollatzPosDens.two_pow_mul_seedBound_one_pow_lt_of_conductor_lt`: if `q_* < 3 · 2^t`, then
  `2^33 𝓜(1)^4 < 2^2^2^(t + 3)`.
* `CollatzPosDens.two_pow_mul_seedBound_one_pow_lt_tower`: `2^33 𝓜(1)^4 < tow_3(140214)`.
* `CollatzPosDens.two_pow_mul_seedBound_one_pow_lt`: the same bound with the tower written out,
  `2^33 𝓜(1)^4 < 2^2^2^140214`.

## Implementation notes

The integer steps are proved for a symbolic exponent `t` and only then specialised to
`t = 140211`, and `tow_3` is unfolded through `tower_three` at a variable top, so that no
tower of literals is ever handed to the kernel for evaluation.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A tower of height three: `tow_3(t) = 2^2^2^t`. -/
theorem tower_three (t : ℕ) : tower 3 t = 2 ^ 2 ^ 2 ^ t := rfl

/-- `log₂ 3 > 25/16`, from the exact integer inequality `3^16 > 2^25`. -/
theorem twentyFive_div_sixteen_lt_logb_two_three : (25 : ℝ) / 16 < Real.logb 2 3 := by
  have h : Real.logb 2 ((2 : ℝ) ^ (25 : ℕ)) < Real.logb 2 ((3 : ℝ) ^ (16 : ℕ)) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  push_cast at h
  linarith

/-- **Step 1 of the seed tower bound.** The conductor satisfies `q_* < 3 · 2^140211`. -/
theorem conductor_lt_three_mul_two_pow : conductor < 3 * 2 ^ 140211 := by
  have h1 := logb_conductor_add_one_lt
  have h2 := sixteen_add_generationThreshold_mul_logGrowthRate_lt
  have h3 := twentyFive_div_sixteen_lt_logb_two_three
  have hq : (0 : ℝ) < conductor := by exact_mod_cast conductor_pos
  have hpos : (0 : ℝ) < 3 * 2 ^ (140211 : ℕ) := by positivity
  have hlog : Real.logb 2 (3 * 2 ^ (140211 : ℕ) : ℝ) = Real.logb 2 3 + 140211 := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    push_cast
    ring
  have hlt : Real.logb 2 (conductor : ℝ) < Real.logb 2 (3 * 2 ^ (140211 : ℕ) : ℝ) := by
    rw [hlog]; linarith
  have := (Real.logb_lt_logb_iff (by norm_num) hq hpos).1 hlt
  exact_mod_cast this

/-- Steps 2 and 3 of the seed tower bound, for a symbolic exponent: if `q_* < 3 · 2^t`, then
`2^33 𝓜(1)^4 < 2^2^2^(t + 3)`. -/
theorem two_pow_mul_seedBound_one_pow_lt_of_conductor_lt {t : ℕ}
    (hq : conductor < 3 * 2 ^ t) : 2 ^ 33 * seedBound 1 ^ 4 < 2 ^ 2 ^ 2 ^ (t + 3) := by
  have hq3 : 3 ≤ conductor := by
    have := nine_mul_generationThreshold_le_conductor
    have := generationThreshold_eq
    omega
  -- Step 2: the exponent.
  have hexp : 2 ^ 33 * seedBound 1 ^ 4 = 2 ^ (185 + 16 * 3 ^ conductor) := by
    rw [seedBound_eq_two_pow, one_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have h27 : 3 ^ 3 ≤ 3 ^ conductor := Nat.pow_le_pow_right (by norm_num) hq3
  have hY1 : 185 + 16 * 3 ^ conductor < 32 * 3 ^ conductor := by norm_num at h27; omega
  have hY2 : 32 * 3 ^ conductor < 2 ^ (5 + 2 * conductor) := by
    have h34 : 3 ^ conductor < 4 ^ conductor :=
      Nat.pow_lt_pow_left (by norm_num) (by omega)
    rw [pow_add, pow_mul]
    norm_num
    omega
  have hY3 : 5 + 2 * conductor < 2 ^ (t + 3) := by
    have hone : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    rw [pow_add]
    generalize 2 ^ t = P at hq hone ⊢
    omega
  have hY : 185 + 16 * 3 ^ conductor < 2 ^ 2 ^ (t + 3) :=
    hY1.trans (hY2.trans (Nat.pow_lt_pow_right (by norm_num) hY3))
  -- Step 3.
  rw [hexp]
  exact Nat.pow_lt_pow_right (by norm_num) hY

/-- The seed tower bound with the tower written out: `2^33 𝓜(1)^4 < 2^2^2^140214`. -/
theorem two_pow_mul_seedBound_one_pow_lt :
    2 ^ 33 * seedBound 1 ^ 4 < 2 ^ 2 ^ 2 ^ 140214 := by
  have h := two_pow_mul_seedBound_one_pow_lt_of_conductor_lt conductor_lt_three_mul_two_pow
  rwa [show 140211 + 3 = 140214 from rfl] at h

/-- **The seed allowance at `s = 1` is below the tower.** `2^33 𝓜(1)^4 < tow_3(140214)`. -/
@[collatz_pos_dens "lem_ph_seed_tower"]
theorem two_pow_mul_seedBound_one_pow_lt_tower :
    2 ^ 33 * seedBound 1 ^ 4 < tower 3 140214 := by
  rw [tower_three]
  exact two_pow_mul_seedBound_one_pow_lt

end CollatzPosDens
