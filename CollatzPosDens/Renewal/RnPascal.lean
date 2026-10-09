/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import CollatzPosDens.Attr

/-!
# The Pascal holding-time law `ϖ`

For `b ∈ ℤ` we set `ϖ(b) = (b - 1) 2^{-b}` if `b ≥ 2` and `ϖ(b) = 0` if `b ≤ 1`. This is the law of
the sum of two independent geometric random variables on `{1, 2, …}` with success probability `1/2`
(a negative binomial, or Pascal, law).

## Main definitions

* `CollatzPosDens.varpi`: the weight `ϖ : ℤ → ℝ`.
* `CollatzPosDens.varpiLast`, `CollatzPosDens.varpiIn`: `ϖ` restricted to the closing letters
  `{4, 5}` and to the nonclosing letters; `varpiLast_add_varpiIn` splits `ϖ` into the two.

## Main results

* `CollatzPosDens.varpi_of_two_le`, `CollatzPosDens.varpi_of_le_one`: the two branches.
* `CollatzPosDens.varpi_natCast_add_two`: `ϖ(n + 2) = (n + 1) (1/2)^(n + 2)`.
* `CollatzPosDens.varpi_nonneg`: every weight is nonnegative.
* `CollatzPosDens.varpi_three`, `varpi_four`, `varpi_five`: the values `1/4`, `3/16`, `1/8`.
* `CollatzPosDens.hasSum_varpi_add_two`: the weights on `b ≥ 2` sum to `1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The Pascal holding-time weight: `ϖ(b) = (b - 1) 2^{-b}` for `b ≥ 2`, and `ϖ(b) = 0`
for `b ≤ 1`. -/
@[collatz_pos_dens "def_rn_pascal"]
noncomputable def varpi (b : ℤ) : ℝ := if 2 ≤ b then ((b : ℝ) - 1) * (2 : ℝ) ^ (-b) else 0

/-- The branch `b ≥ 2` of `ϖ`. -/
lemma varpi_of_two_le {b : ℤ} (hb : 2 ≤ b) : varpi b = ((b : ℝ) - 1) * (2 : ℝ) ^ (-b) := by
  simp [varpi, hb]

/-- The branch `b ≤ 1` of `ϖ`. -/
lemma varpi_of_le_one {b : ℤ} (hb : b ≤ 1) : varpi b = 0 := by
  simp [varpi, show ¬ 2 ≤ b by omega]

/-- `ϖ` vanishes below `2`: a letter of nonzero weight is at least `2`. -/
lemma two_le_of_varpi_ne_zero {b : ℤ} (h : varpi b ≠ 0) : 2 ≤ b := by
  by_contra h'
  exact h (varpi_of_le_one (by omega))

/-- Every Pascal weight is nonnegative. -/
lemma varpi_nonneg (b : ℤ) : 0 ≤ varpi b := by
  unfold varpi
  split_ifs with hb
  · have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have : (0 : ℝ) ≤ (b : ℝ) - 1 := by linarith
    positivity
  · exact le_rfl

/-- `ϖ(n + 2) = (n + 1) (1/2)^(n + 2)` for `n ∈ ℕ`. -/
lemma varpi_natCast_add_two (n : ℕ) : varpi ((n : ℤ) + 2) = (n + 1) * (1 / 2) ^ (n + 2) := by
  have h : -((n : ℤ) + 2) = -((n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [varpi_of_two_le (by omega), h, zpow_neg, zpow_natCast, one_div_pow, one_div]
  push_cast
  ring

/-- `ϖ(3) = 1/4`. -/
lemma varpi_three : varpi 3 = 1 / 4 := by rw [varpi_of_two_le (by norm_num)]; norm_num

/-- `ϖ(4) = 3/16`. -/
lemma varpi_four : varpi 4 = 3 / 16 := by rw [varpi_of_two_le (by norm_num)]; norm_num

/-- `ϖ(5) = 1/8`. -/
lemma varpi_five : varpi 5 = 1 / 8 := by rw [varpi_of_two_le (by norm_num)]; norm_num

/-- `ϖ` restricted to the closing letters `{4, 5}`. -/
noncomputable def varpiLast (b : ℤ) : ℝ := if b ∈ ({4, 5} : Set ℤ) then varpi b else 0

/-- `ϖ` restricted to the nonclosing letters `b ∉ {4, 5}`. -/
noncomputable def varpiIn (b : ℤ) : ℝ := if b ∉ ({4, 5} : Set ℤ) then varpi b else 0

/-- On a closing letter `b ∈ {4, 5}`, `ϖ_last(b) = ϖ(b)`. -/
lemma varpiLast_of_mem {b : ℤ} (h : b ∈ ({4, 5} : Set ℤ)) : varpiLast b = varpi b := by
  simp [varpiLast, h]

/-- On a nonclosing letter `b ∉ {4, 5}`, `ϖ_last(b) = 0`. -/
lemma varpiLast_of_notMem {b : ℤ} (h : b ∉ ({4, 5} : Set ℤ)) : varpiLast b = 0 := by
  simp [varpiLast, h]

/-- On a closing letter `b ∈ {4, 5}`, `ϖ_in(b) = 0`. -/
lemma varpiIn_of_mem {b : ℤ} (h : b ∈ ({4, 5} : Set ℤ)) : varpiIn b = 0 := by
  simp [varpiIn, h]

/-- On a nonclosing letter `b ∉ {4, 5}`, `ϖ_in(b) = ϖ(b)`. -/
lemma varpiIn_of_notMem {b : ℤ} (h : b ∉ ({4, 5} : Set ℤ)) : varpiIn b = varpi b := by
  simp [varpiIn, h]

/-- `ϖ_in(b) = 0` for `b ≤ 1`. -/
lemma varpiIn_of_le_one {b : ℤ} (hb : b ≤ 1) : varpiIn b = 0 := by
  simp [varpiIn, varpi_of_le_one hb]

/-- Every weight `ϖ_last(b)` is nonnegative. -/
lemma varpiLast_nonneg (b : ℤ) : 0 ≤ varpiLast b := by
  unfold varpiLast; split_ifs <;> simp [varpi_nonneg]

/-- Every weight `ϖ_in(b)` is nonnegative. -/
lemma varpiIn_nonneg (b : ℤ) : 0 ≤ varpiIn b := by
  unfold varpiIn; split_ifs <;> simp [varpi_nonneg]

/-- `ϖ = ϖ_last + ϖ_in`: every letter is either closing or nonclosing. -/
lemma varpiLast_add_varpiIn (b : ℤ) : varpiLast b + varpiIn b = varpi b := by
  by_cases h : b ∈ ({4, 5} : Set ℤ)
  · rw [varpiLast_of_mem h, varpiIn_of_mem h, add_zero]
  · rw [varpiLast_of_notMem h, varpiIn_of_notMem h, zero_add]

/-- The weights `ϖ(b)`, `b ≥ 2`, form a probability distribution. -/
lemma hasSum_varpi_add_two : HasSum (fun n : ℕ ↦ varpi ((n : ℤ) + 2)) 1 := by
  simp_rw [varpi_natCast_add_two]
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 2) (by norm_num)
  have h2 := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have := ((h1.add h2).mul_left ((1 / 2) ^ 2))
  convert this using 1
  · ext n; ring
  · norm_num

end CollatzPosDens
