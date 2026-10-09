/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Monotone.MoLogSqrt

/-!
# A logarithmic budget for the mixing estimates

For an integer $n \ge 2^{80}$ and reals $D, \eta \ge 0$ with $D \le \eta \cdot 2^{40}$, we have
$D \log n \le \eta\, n$. The proof combines $\log n \le \sqrt n$ with $\sqrt n \ge 2^{40}$.

## Main results

* `CollatzPosDens.mul_log_le_mul_of_two_pow_eighty_le`: the budget inequality.

## Implementation notes

The hypothesis $\eta \ge 0$ is omitted, since it follows from $0 \le D \le \eta \cdot 2^{40}$.

## References

* [Mazur, *Collatz positive density*, §13.4]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `n ≥ 2 ^ 80` and `0 ≤ D ≤ η * 2 ^ 40`, then `D * log n ≤ η * n`. -/
@[collatz_pos_dens "lem_mx_log_budget"]
theorem mul_log_le_mul_of_two_pow_eighty_le {n : ℕ} (hn : 2 ^ 80 ≤ n) {D η : ℝ}
    (hD : 0 ≤ D) (hDη : D ≤ η * 2 ^ 40) : D * Real.log n ≤ η * n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hη : 0 ≤ η := by linarith
  have hs : (2 : ℝ) ^ 40 ≤ Real.sqrt n :=
    Real.le_sqrt_of_sq_le (by rw [← pow_mul]; exact_mod_cast hn)
  calc D * Real.log n ≤ D * Real.sqrt n := mul_le_mul_of_nonneg_left (log_le_sqrt hn0) hD
    _ ≤ η * 2 ^ 40 * Real.sqrt n := mul_le_mul_of_nonneg_right hDη (Real.sqrt_nonneg _)
    _ ≤ η * Real.sqrt n * Real.sqrt n := by gcongr
    _ = η * n := by rw [mul_assoc, Real.mul_self_sqrt hn0]

end CollatzPosDens
