/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr

/-!
# A moment generating function bound for the geometric distribution

Let `A` be a geometric random variable with `P(A = a) = 2⁻ᵃ` for `a ≥ 1`, so that `E[A] = 2`.
For real `θ` with `|θ| ≤ 1/4` its centred moment generating function satisfies
$$\sum_{a \ge 1} 2^{-a} e^{\theta (a - 2)} \le e^{8 \theta^2}.$$

The proof sums the geometric series to `e^{-θ} / (2 - e^θ) = 1 / (1 - s)` with
`s = (e^θ - 1)²`, bounds `s ≤ 4 θ² ≤ 1/4` using `|e^θ - 1| ≤ 2 |θ|`, and concludes from
`1 / (1 - s) ≤ 1 + 2 s ≤ e^{2 s} ≤ e^{8 θ²}`.

## Main results

* `CollatzPosDens.tsum_geometric_mul_exp_le`: the bound above.

## Implementation notes

The sum over `a ≥ 1` is written as a sum over `n : ℕ` with `a = n + 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- For `|θ| ≤ 1/4`, the centred moment generating function of the geometric distribution
satisfies `∑_{a ≥ 1} 2⁻ᵃ e^{θ (a - 2)} ≤ e^{8 θ²}`, the sum indexed by `a = n + 1`. -/
@[collatz_pos_dens "lem_mgf_bound"]
theorem tsum_geometric_mul_exp_le (θ : ℝ) (hθ : |θ| ≤ 1 / 4) :
    ∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * exp (θ * (((n + 1 : ℕ) : ℝ) - 2)) ≤
      exp (8 * θ ^ 2) := by
  set e := exp θ with he_def
  have he : 0 < e := exp_pos θ
  have hs : |e - 1| ≤ 2 * |θ| := abs_exp_sub_one_le (by linarith)
  have hθ2 : θ ^ 2 ≤ 1 / 16 := by
    have := sq_abs θ
    nlinarith [abs_nonneg θ]
  have hsq : (e - 1) ^ 2 ≤ 4 * θ ^ 2 := by
    have := sq_abs (e - 1)
    have := sq_abs θ
    nlinarith [abs_nonneg (e - 1), abs_nonneg θ]
  have hlt : e < 2 := by nlinarith [sq_nonneg (e - 1)]
  have hterm : ∀ n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * exp (θ * (((n + 1 : ℕ) : ℝ) - 2)) =
      exp (-θ) / 2 * (e / 2) ^ n := by
    intro n
    have : θ * (((n + 1 : ℕ) : ℝ) - 2) = n * θ + -θ := by push_cast; ring
    rw [this, exp_add, exp_nat_mul, ← he_def, div_pow, pow_succ, inv_pow]
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by linarith)]
  have key : 1 ≤ exp (8 * θ ^ 2) * (e * (2 - e)) := by
    have h1 : 1 + 2 * (e - 1) ^ 2 ≤ exp (8 * θ ^ 2) := by
      have := add_one_le_exp (2 * (e - 1) ^ 2)
      have := exp_le_exp.2 (show 2 * (e - 1) ^ 2 ≤ 8 * θ ^ 2 by linarith)
      linarith
    have h2 : e * (2 - e) = 1 - (e - 1) ^ 2 := by ring
    rw [h2]
    nlinarith [sq_nonneg (e - 1)]
  have hne : exp (-θ) * e = 1 := by rw [he_def, ← exp_add]; simp
  have h2e : 0 < 2 - e := by linarith
  have : exp (-θ) / 2 * (1 - e / 2)⁻¹ = exp (-θ) / (2 - e) := by
    field_simp
  rw [this, div_le_iff₀ h2e]
  have hpos : 0 < exp (-θ) := exp_pos _
  nlinarith [exp_pos (8 * θ ^ 2)]

end CollatzPosDens
