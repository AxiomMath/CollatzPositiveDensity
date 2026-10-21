/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06ClipFloor

/-!
# The degree floor caps the dyadic tail

For every `m ∈ ℕ` and every real `B > 0`, the clipping degree floor
`clipFloor m B = ⌈log₂(8 · 3^m / B)⌉` satisfies `3^m · 2^(-clipFloor m B) ≤ B / 8`: since
`clipFloor m B ≥ log₂(8 · 3^m / B)` and `x ↦ 2^x` is increasing, `2^(clipFloor m B) ≥ 8 · 3^m / B`.

## Main results

* `CollatzPosDens.three_pow_mul_two_zpow_neg_clipFloor_le`: `3^m · 2^(-clipFloor m B) ≤ B / 8`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `m ∈ ℕ` and real `B > 0`, `3^m · 2^(-clipFloor m B) ≤ B / 8`. -/
@[collatz_pos_dens "lem_s06_clip_floor_cap"]
theorem three_pow_mul_two_zpow_neg_clipFloor_le (m : ℕ) {B : ℝ} (hB : 0 < B) :
    (3 : ℝ) ^ m * (2 : ℝ) ^ (-clipFloor m B) ≤ B / 8 := by
  rw [zpow_neg, ← div_eq_mul_inv]
  exact three_pow_div_two_zpow_le hB le_rfl

end CollatzPosDens
