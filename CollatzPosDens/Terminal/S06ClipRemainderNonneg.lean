/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06ClipRemainder
public import CollatzPosDens.Terminal.S06ClipLeRef

/-!
# The clipping remainder is nonnegative

For every `y : ResidueGroup q`, the clipping remainder `clipRemainder q n B y` is nonnegative.
If `q ≤ n` it equals `refDensity q y - clipDensity q n B y`; if `n < q` it equals
`refDensity n x - clipDensity n n B x` plus an absolute value, where `x = residueReduction _ y`.
Both differences are nonnegative by `clipDensity_le_refDensity`.

## Main results

* `CollatzPosDens.clipRemainder_nonneg`: `0 ≤ clipRemainder q n B y`.

## Implementation notes

The statement in [Mazur] assumes `q ≥ 1`, `n ≥ 2` and `B > 0`; the bound holds for all
`q, n ∈ ℕ` and real `B`, and is stated so.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The clipping remainder is nonnegative.** For every `y : ResidueGroup q`,
`0 ≤ clipRemainder q n B y`. -/
@[collatz_pos_dens "lem_s06_clip_remainder_nonneg"]
theorem clipRemainder_nonneg (q n : ℕ) (B : ℝ) (y : ResidueGroup q) :
    0 ≤ clipRemainder q n B y := by
  rcases le_or_gt q n with h | h
  · rw [clipRemainder_of_le h]
    exact sub_nonneg.2 (clipDensity_le_refDensity q n B y)
  · rw [clipRemainder_of_lt h]
    exact add_nonneg (sub_nonneg.2 (clipDensity_le_refDensity n n B _)) (abs_nonneg _)

end CollatzPosDens
