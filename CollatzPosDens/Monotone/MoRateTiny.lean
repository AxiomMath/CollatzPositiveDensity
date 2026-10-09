/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Monotone.MoRate
public import Mathlib.Analysis.Complex.Exponential

/-!
# The white-case rate is tiny near the top

Let `A ≥ 0` be real and `m` a natural number with `log m ≥ 32`. Writing `U = log m` and
`t = moRate A m = 4A(1 + U)/m`, one has `8 t m / U² = 32 A (1 + U) / U² ≤ 33 A / U` since
`U ≥ 32`, and, since `m = e^U ≥ U⁴/24` and `U³ ≥ 256 (1 + U)`, also
`8 t = 32 A (1 + U)/m ≤ 3 A / U`. Adding, `8 t (m / (log m)² + 1) ≤ 36 A / log m`.

## Main results

* `CollatzPosDens.moRate_tiny`: `8 · moRate A m · (m / (log m)² + 1) ≤ 36 A / log m`.

## Implementation notes

No hypothesis `m ≥ 2` is imposed: it is implied by `log m ≥ 32`, since `log m = 0` for
`m ∈ {0, 1}`.

## References

* [Mazur, *Collatz positive density*], §8.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `A ≥ 0` and `log m ≥ 32`, `8 · moRate A m · (m / (log m)² + 1) ≤ 36 A / log m`. -/
@[collatz_pos_dens "lem_mo_rate_tiny"]
theorem moRate_tiny {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 32 ≤ Real.log m) :
    8 * moRate A m * (m / Real.log m ^ 2 + 1) ≤ 36 * A / Real.log m := by
  set U := Real.log m with hU
  have hU0 : 0 < U := by linarith
  have hm0 : (0 : ℝ) < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · norm_num [hU, h0] at hm
    · exact_mod_cast h0
  have hexp : Real.exp U = m := Real.exp_log hm0
  have h4 : U ^ 4 / 24 ≤ (m : ℝ) := by
    simpa [hexp, Nat.factorial] using Real.pow_div_factorial_le_exp U hU0.le 4
  have h1 : 8 * moRate A m * (m / U ^ 2) ≤ 33 * A / U := by
    have : 8 * moRate A m * (m / U ^ 2) = 32 * A * (1 + U) / U ^ 2 := by
      rw [moRate_def, ← hU]
      field_simp
      ring
    rw [this, div_le_div_iff₀ (by positivity) hU0]
    nlinarith [mul_nonneg (mul_nonneg hA hU0.le) (sub_nonneg.2 hm)]
  have h2 : 8 * moRate A m ≤ 3 * A / U := by
    rw [moRate_def, ← hU, mul_div_assoc', div_le_div_iff₀ hm0 hU0]
    have hU3 : 256 * (1 + U) ≤ U ^ 3 := by nlinarith
    have hkey : 32 * U * (1 + U) ≤ 3 * m := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hkey hA]
  calc 8 * moRate A m * (m / U ^ 2 + 1) = 8 * moRate A m * (m / U ^ 2) + 8 * moRate A m := by
        ring
    _ ≤ 33 * A / U + 3 * A / U := add_le_add h1 h2
    _ = 36 * A / U := by ring

end CollatzPosDens
