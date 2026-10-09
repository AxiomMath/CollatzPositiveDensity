/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Algebra.Field.GeomSum
public import CollatzPosDens.Attr

/-!
# Orthogonality of the `N`-th roots of unity

For an integer `N ≥ 1` and an integer `a`,
$$\sum_{t=0}^{N-1} \exp(2\pi i\, a t / N) = \begin{cases} N & N \mid a, \\ 0 & \text{otherwise}.
\end{cases}$$
With `ζ = exp(2πi a / N)` the sum is the geometric sum `∑ ζ ^ t`; if `N ∣ a` then `ζ = 1`,
and otherwise `ζ ≠ 1` while `ζ ^ N = 1`, so the geometric sum vanishes.

## Main results

* `CollatzPosDens.sum_exp_two_pi_mul_I_mul_div`: for `N ≠ 0`, `∑ t ∈ range N, exp (2πi a t / N)`
  equals `N` if `(N : ℤ) ∣ a` and `0` otherwise.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Finset Real

/-- Orthogonality of the `N`-th roots of unity: `∑_{t < N} exp(2πi a t / N)` equals `N` when
`N ∣ a` and `0` otherwise. -/
@[collatz_pos_dens "lem_mx_root_sum"]
theorem sum_exp_two_pi_mul_I_mul_div {N : ℕ} (hN : N ≠ 0) (a : ℤ) :
    ∑ t ∈ range N, exp (2 * π * I * a * t / N) = if (N : ℤ) ∣ a then (N : ℂ) else 0 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set ζ : ℂ := exp (2 * π * I * a / N) with hζ
  have hterm : ∀ t : ℕ, exp (2 * π * I * a * t / N) = ζ ^ t := fun t => by
    rw [hζ, ← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hterm]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    have : ζ = 1 := by
      rw [hζ]
      convert exp_int_mul_two_pi_mul_I k using 2
      push_cast; field_simp
    simp [this]
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      obtain ⟨n, hn⟩ := exp_eq_one_iff.mp h1
      apply h
      refine ⟨n, ?_⟩
      have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have : (a : ℂ) = N * n := by
        have h2 : 2 * π * I * a = (N * n) * (2 * π * I) := by
          rw [div_eq_iff hN'] at hn; linear_combination hn
        exact mul_left_cancel₀ hpi (by linear_combination h2)
      exact_mod_cast this
    have hζN : ζ ^ N = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      convert exp_int_mul_two_pi_mul_I a using 2
      field_simp
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]

end CollatzPosDens
