/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The moment generating function of a centred geometric variable

Let `A` be geometric on `{1, 2, …}` with `ℙ(A = a) = 2^{-a}`, so that `𝔼 A = 2`. Its centred
moment generating function is `φ(t) = ∑_{a ≥ 1} 2^{-a} e^{t(a-2)}`. For `|t| ≤ 1/32` we show
`1 ≤ φ(t) ≤ e^{9t²/8}`.

For `e^t < 2` the geometric series gives the closed form `φ(t) = e^{-t} / (2 - e^t)`. Writing
`u = e^t`, the lower bound is `u + u⁻¹ ≥ 2`. For the upper bound, `u (2 - u) = 1 - (u - 1)²`
and `e^{s} ≥ 1 + s` with `s = 9t²/8` reduce the claim to `(u - 1)² (1 + s) ≤ s`, which follows
from `|u - 1| ≤ |t| + t² ≤ (33/32)|t|` and `t² ≤ 1/1024`.

## Main results

* `CollatzPosDens.fcMgf_hasSum`: the closed form `φ(t) = e^{-t}/(2 - e^t)` when `e^t < 2`.
* `CollatzPosDens.fcMgf_bounds`: `1 ≤ φ(t) ≤ e^{9t²/8}` for `|t| ≤ 1/32`.

## Implementation notes

The sum over `a ≥ 1` is indexed by `a + 1` with `a : ℕ`. Instead of applying Taylor's formula
to `κ = log φ` with the estimate `κ'' ≤ 496/225`, we compare `φ(t)` and `e^{9t²/8}` directly
through the elementary bounds `|e^t - 1 - t| ≤ t²` and `1 + s ≤ e^s`, which give the same
constant `9/8`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- Closed form of the centred geometric moment generating function: for `e^t < 2`,
`∑_{a ≥ 1} 2^{-a} e^{t(a-2)} = e^{-t} / (2 - e^t)`. -/
theorem fcMgf_hasSum {t : ℝ} (ht : exp t < 2) :
    HasSum (fun a : ℕ => (1 / 2 : ℝ) ^ (a + 1) * exp (t * (((a + 1 : ℕ) : ℝ) - 2)))
      (exp (-t) / (2 - exp t)) := by
  have hg := (hasSum_geometric_of_lt_one (by positivity) (by linarith : exp t / 2 < 1)).mul_left
    (exp (-t) / 2)
  convert hg using 1
  · funext a
    rw [show exp (t * (((a + 1 : ℕ) : ℝ) - 2)) = exp (-t) * exp t ^ a by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring_nf]
    ring
  · have : (2 : ℝ) - exp t ≠ 0 := by linarith
    field_simp

/-- **Bounds on the centred geometric moment generating function.** For `|t| ≤ 1/32`,
`1 ≤ ∑_{a ≥ 1} 2^{-a} e^{t(a-2)} ≤ e^{9t²/8}`. -/
@[collatz_pos_dens "lem_fc_mgf"]
theorem fcMgf_bounds {t : ℝ} (ht : |t| ≤ 1 / 32) :
    1 ≤ ∑' a : ℕ, (1 / 2 : ℝ) ^ (a + 1) * exp (t * (((a + 1 : ℕ) : ℝ) - 2)) ∧
      ∑' a : ℕ, (1 / 2 : ℝ) ^ (a + 1) * exp (t * (((a + 1 : ℕ) : ℝ) - 2)) ≤
        exp (9 * t ^ 2 / 8) := by
  have hab := abs_le.mp ht
  have hexp := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := t) (by linarith))
  set u := exp t
  have hupos : 0 < u := exp_pos t
  have hu2 : u < 2 := by nlinarith
  rw [(fcMgf_hasSum hu2).tsum_eq, Real.exp_neg]
  have hd : 0 < 2 - u := by linarith
  have hsq : (u - 1) ^ 2 ≤ (33 / 32) ^ 2 * t ^ 2 := by
    have h1 : |u - 1| ≤ 33 / 32 * |t| := by
      rw [abs_le]
      rcases abs_cases t with ⟨h, h0⟩ | ⟨h, h0⟩ <;> rw [h] <;> constructor <;> nlinarith
    simpa [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) h1 2
  constructor
  · rw [le_div_iff₀ hd, one_mul]
    nlinarith [sq_nonneg (u - 1), inv_pos.mpr hupos, inv_mul_cancel₀ hupos.ne']
  · rw [div_le_iff₀ hd]
    have key : 1 ≤ u * (2 - u) * exp (9 * t ^ 2 / 8) := by
      have hcore : (u - 1) ^ 2 * (1 + 9 * t ^ 2 / 8) ≤ 9 * t ^ 2 / 8 := by
        nlinarith [sq_nonneg t, show t ^ 2 ≤ 1 / 1024 by nlinarith]
      nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (9 * t ^ 2 / 8))
        (by positivity : 0 ≤ u * (2 - u))]
    nlinarith [inv_pos.mpr hupos, inv_mul_cancel₀ hupos.ne']

end CollatzPosDens
