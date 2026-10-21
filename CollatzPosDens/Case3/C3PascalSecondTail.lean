/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import Mathlib.Tactic.LinearCombination

/-!
# First moments of the Pascal tails

For the Pascal weights `ϖ(b) = (b - 1) 2^{-b}` (`b ≥ 2`), `ϖ(b) = 0` (`b ≤ 1`), the first moment of
the tail beyond any `m ∈ ℕ` is explicit: `∑_{b ∈ ℤ, b > m} b ϖ(b) = (m² + 3m + 4) 2^{-m}`.
In particular (`m = 0`) the Pascal law has mean `∑_b b ϖ(b) = 4`.

The case `m = 0` is `∑_{n ≥ 0} (n + 2)(n + 1) 2^{-(n+2)} = 4`, the binomial series
`∑_n C(n + 2, 2) x^n = (1 - x)^{-3}` at `x = 1/2`; the general case follows by induction on `m`,
removing the term `(m + 1) ϖ(m + 1) = (m + 1) m 2^{-(m+1)}` at each step.

## Main results

* `CollatzPosDens.hasSum_mul_varpi_indicator_Ioi`: `∑_{b > m} b ϖ(b) = (m² + 3m + 4) 2^{-m}`, as an
  unconditionally convergent series over `ℤ` of the moments restricted to `b > m`.
* `CollatzPosDens.hasSum_mul_varpi_Ioi`: the same series indexed by the subtype `{b : ℤ // m < b}`.
* `CollatzPosDens.tsum_mul_varpi_Ioi`: the value of the tail moment as a `tsum`.
* `CollatzPosDens.hasSum_mul_varpi`: the mean `∑_{b ∈ ℤ} b ϖ(b) = 4`.

## Implementation notes

The restricted sum `∑_{b ∈ ℤ, b > m}` is formalized as the series of
`Set.indicator (Set.Ioi m) (fun b ↦ b ϖ(b))` over `ℤ`, in the strong (`HasSum`, unconditional)
form; the subtype and `tsum` forms follow.

## References

* [Mazur, *Collatz positive density*], §10.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The mean of the Pascal law: `∑_{b ∈ ℤ} b ϖ(b) = 4`. -/
theorem hasSum_mul_varpi : HasSum (fun b : ℤ ↦ (b : ℝ) * varpi b) 4 := by
  have hg : Function.Injective (fun n : ℕ ↦ (n : ℤ) + 2) := fun a b h ↦ by
    simpa using h
  refine (hg.hasSum_iff fun b hb ↦ ?_).mp ?_
  · rw [varpi_of_le_one, mul_zero]
    by_contra h
    exact hb ⟨(b - 2).toNat, by simp only; omega⟩
  · have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2
      (r := 1 / 2) (by norm_num)).mul_left (1 / 2)
    convert h using 1
    · ext n
      have hc : ((n + 2).choose 2 : ℝ) * 2 = ((n : ℝ) + 2) * (n + 1) := by
        have : (n + 2).choose 2 * 2 = (n + 2) * (n + 1) := by
          rw [Nat.choose_two_right]
          exact Nat.div_mul_cancel (Nat.even_mul_pred_self _).two_dvd
        exact_mod_cast this
      simp only [Function.comp_apply, varpi_natCast_add_two]
      push_cast
      linear_combination (-(1 / 4) * (1 / 2 : ℝ) ^ n) * hc
    · norm_num

/-- First moments of the Pascal tails: `∑_{b ∈ ℤ, b > m} b ϖ(b) = (m² + 3m + 4) 2^{-m}` for every
`m ∈ ℕ`. -/
@[collatz_pos_dens "lem_c3_pascal_second_tail"]
theorem hasSum_mul_varpi_indicator_Ioi (m : ℕ) :
    HasSum ((Set.Ioi (m : ℤ)).indicator fun b ↦ (b : ℝ) * varpi b)
      (((m : ℝ) ^ 2 + 3 * m + 4) * (2 : ℝ) ^ (-(m : ℤ))) := by
  induction m with
  | zero =>
    convert hasSum_mul_varpi using 1
    · ext b
      by_cases hb : (0 : ℤ) < b
      · simp [hb]
      · simp [hb, varpi_of_le_one (by omega : b ≤ 1)]
    · norm_num
  | succ m ih =>
    convert ih.sub (hasSum_pi_single ((m : ℤ) + 1) (((m : ℝ) + 1) * varpi ((m : ℤ) + 1))) using 1
    · ext b
      by_cases hb : b = (m : ℤ) + 1
      · simp [hb]
      · simp only [Set.indicator, Set.mem_Ioi, Pi.single_apply, hb, ite_false, sub_zero]
        grind
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · norm_num [varpi_of_le_one]
      · rw [varpi_of_two_le (by omega), show -(((m + 1 : ℕ) : ℤ)) = -(m : ℤ) - 1 by push_cast; ring,
          show -((m : ℤ) + 1) = -(m : ℤ) - 1 by ring, zpow_sub₀ two_ne_zero]
        push_cast
        field_simp
        ring

/-- First moments of the Pascal tails, indexed by the subtype `{b : ℤ // m < b}`. -/
theorem hasSum_mul_varpi_Ioi (m : ℕ) :
    HasSum (fun b : Set.Ioi (m : ℤ) ↦ (b : ℝ) * varpi b)
      (((m : ℝ) ^ 2 + 3 * m + 4) * (2 : ℝ) ^ (-(m : ℤ))) :=
  hasSum_subtype_iff_indicator.mpr (hasSum_mul_varpi_indicator_Ioi m)

/-- `∑_{b > m} b ϖ(b) = (m² + 3m + 4) 2^{-m}`, as a `tsum`. -/
theorem tsum_mul_varpi_Ioi (m : ℕ) :
    ∑' b : Set.Ioi (m : ℤ), (b : ℝ) * varpi b =
      ((m : ℝ) ^ 2 + 3 * m + 4) * (2 : ℝ) ^ (-(m : ℤ)) :=
  (hasSum_mul_varpi_Ioi m).tsum_eq

end CollatzPosDens
