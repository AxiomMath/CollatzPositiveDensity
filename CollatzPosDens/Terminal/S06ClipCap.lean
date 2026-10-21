/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06ClipWidth

/-!
# The clipping offset cap

For integers `m ≥ 1`, `n ≥ 2` and a real `B > 0`, the *clipping offset cap* is the real number
$$L^{\mathrm{clp}}_{m,n,B} = \frac{B}{4\,(2 w^{\mathrm{clp}}_{m,n} + 1)},$$
where $w^{\mathrm{clp}}_{m,n}$ is the clipping width `clipWidth m n`.

## Main definitions

* `CollatzPosDens.clipCap m n B`: the clipping offset cap `L^clp_{m,n,B}`.

## Main results

* `CollatzPosDens.clipCap_pos`: `L^clp_{m,n,B} > 0` for `B > 0`.
* `CollatzPosDens.mul_clipCap`: `4 (2 w^clp_{m,n} + 1) L^clp_{m,n,B} = B`.

## Implementation notes

The definition makes sense for every real `B`; positivity (`clipCap_pos`) requires `B > 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping offset cap `L^clp_{m,n,B} = B / (4 (2 w^clp_{m,n} + 1)) ∈ ℝ`. -/
@[collatz_pos_dens "def_s06_clip_cap"]
noncomputable def clipCap (m n : ℕ) (B : ℝ) : ℝ :=
  B / (4 * (2 * clipWidth m n + 1))

/-- Unfolding lemma for `clipCap`. -/
theorem clipCap_def (m n : ℕ) (B : ℝ) :
    clipCap m n B = B / (4 * (2 * clipWidth m n + 1)) :=
  rfl

/-- The denominator `4 (2 w^clp_{m,n} + 1)` of the cap is positive. -/
theorem clipCap_denom_pos (m n : ℕ) : (0 : ℝ) < 4 * (2 * clipWidth m n + 1) := by
  positivity

/-- The clipping offset cap is positive when `B` is. -/
theorem clipCap_pos (m n : ℕ) {B : ℝ} (hB : 0 < B) : 0 < clipCap m n B :=
  div_pos hB (clipCap_denom_pos m n)

/-- The clipping offset cap is nonnegative when `B` is. -/
theorem clipCap_nonneg (m n : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 ≤ clipCap m n B :=
  div_nonneg hB (clipCap_denom_pos m n).le

/-- `4 (2 w^clp_{m,n} + 1) L^clp_{m,n,B} = B`. -/
theorem mul_clipCap (m n : ℕ) (B : ℝ) : 4 * (2 * clipWidth m n + 1) * clipCap m n B = B :=
  mul_div_cancel₀ B (clipCap_denom_pos m n).ne'

end CollatzPosDens
