/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06CountLevel

/-!
# The clipping height of the count

For an integer `t ≥ 1`, the *clipping height of the count* is the real number
$$B_{\mathrm{ct}}(t) = 2^{52}\, t\, \sqrt{n_{\mathrm{ct}}(t) \log n_{\mathrm{ct}}(t)},$$
with `log` the natural logarithm and `n_ct(t)` the clipping level `CollatzPosDens.countLevel`.

## Main definitions

* `CollatzPosDens.countHeight t`: the clipping height `B_ct(t)`.

## Main results

* `CollatzPosDens.countHeight_nonneg`: `0 ≤ B_ct(t)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping height of the count, `B_ct(t) = 2^{52} t √(n_ct(t) log n_ct(t)) ∈ ℝ`, with `log`
the natural logarithm. -/
@[collatz_pos_dens "def_s06_count_height"]
noncomputable def countHeight (t : ℕ) : ℝ :=
  2 ^ 52 * (t : ℝ) * √((countLevel t : ℝ) * Real.log (countLevel t))

/-- Unfolding lemma for `countHeight`. -/
theorem countHeight_def (t : ℕ) :
    countHeight t = 2 ^ 52 * (t : ℝ) * √((countLevel t : ℝ) * Real.log (countLevel t)) :=
  rfl

/-- The clipping height is nonnegative. -/
theorem countHeight_nonneg (t : ℕ) : 0 ≤ countHeight t := by
  rw [countHeight_def]; positivity

end CollatzPosDens
