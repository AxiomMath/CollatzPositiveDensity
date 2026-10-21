/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06CountX

/-!
# The clipping level of the count

For an integer `t ≥ 1`, the *clipping level of the count* is the natural number
`n_ct(t) = ⌈x_ct(t)⌉`, the ceiling of the clipping base `CollatzPosDens.countX`.

## Main definitions

* `CollatzPosDens.countLevel t`: the clipping level `n_ct(t)`.

## Main results

* `CollatzPosDens.countX_le_countLevel`: `x_ct(t) ≤ n_ct(t)`.
* `CollatzPosDens.countLevel_lt`: `n_ct(t) < x_ct(t) + 1`.
* `CollatzPosDens.countLevel_le_two_mul`: `n_ct(t) ≤ 2 x_ct(t)` for `t ≥ 1`.
* `CollatzPosDens.countLevel_pos`: `0 < n_ct(t)` for `t ≥ 1`.

## Implementation notes

The clipping base is a nonnegative real, so the ceiling is `Nat.ceil`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping level of the count, `n_ct(t) = ⌈x_ct(t)⌉ ∈ ℕ`. -/
@[collatz_pos_dens "def_s06_count_level"]
noncomputable def countLevel (t : ℕ) : ℕ := ⌈countX t⌉₊

/-- Unfolding lemma for `countLevel`. -/
theorem countLevel_def (t : ℕ) : countLevel t = ⌈countX t⌉₊ := rfl

/-- The clipping base is at most the clipping level: `x_ct(t) ≤ n_ct(t)`. -/
theorem countX_le_countLevel (t : ℕ) : countX t ≤ countLevel t := Nat.le_ceil _

/-- The clipping level is below the clipping base plus one: `n_ct(t) < x_ct(t) + 1`. -/
theorem countLevel_lt (t : ℕ) : (countLevel t : ℝ) < countX t + 1 :=
  Nat.ceil_lt_add_one (countX_nonneg t)

/-- The clipping level is at most twice the clipping base, for `t ≥ 1`:
`n_ct(t) ≤ 2 x_ct(t)`. -/
theorem countLevel_le_two_mul {t : ℕ} (ht : 1 ≤ t) : (countLevel t : ℝ) ≤ 2 * countX t := by
  linarith [countLevel_lt t, one_le_countX ht]

/-- The clipping level is positive for `t ≥ 1`. -/
theorem countLevel_pos {t : ℕ} (ht : 1 ≤ t) : 0 < countLevel t :=
  Nat.ceil_pos.mpr (countX_pos ht)

end CollatzPosDens
