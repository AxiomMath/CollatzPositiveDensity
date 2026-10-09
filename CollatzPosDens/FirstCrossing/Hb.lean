/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Wb

/-!
# The scale parameter `h_b`

For a natural number `b` this file defines the scale parameter
$$h_b = b + w_b,$$
where `w_b = ⌊3b/5⌋` is `CollatzPosDens.wb`.

## Main definitions

* `CollatzPosDens.hb`: the parameter `h_b = b + w_b`.

## Main results

* `CollatzPosDens.hb_def`: the unfolding `h_b = b + w_b`.
* `CollatzPosDens.hb_eq`: the closed form `h_b = b + 3b/5` (natural-number division).
* `CollatzPosDens.le_hb`, `CollatzPosDens.hb_le_two_mul`: the bounds `b ≤ h_b ≤ 2b`.
* `CollatzPosDens.lt_hb`: `b < h_b` for `b ≥ 2`.
* `CollatzPosDens.hb_mono`: `h_b` is monotone in `b`.

## References

* [Mazur, *Collatz positive density*], §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale parameter `h_b = b + w_b`, for `b : ℕ`. -/
@[collatz_pos_dens "def_hb"]
def hb (b : ℕ) : ℕ := b + wb b

/-- Unfolding lemma for `hb`. -/
theorem hb_def (b : ℕ) : hb b = b + wb b := rfl

/-- Closed form `h_b = b + ⌊3b/5⌋`, with the floor computed as natural-number division. -/
theorem hb_eq (b : ℕ) : hb b = b + 3 * b / 5 := rfl

/-- `b ≤ h_b`. -/
theorem le_hb (b : ℕ) : b ≤ hb b := Nat.le_add_right b _

/-- `h_b ≤ 2b`. -/
theorem hb_le_two_mul (b : ℕ) : hb b ≤ 2 * b := by
  have := wb_le_self b
  rw [hb_def]; omega

/-- `b < h_b` as soon as `w_b > 0`, i.e. for `b ≥ 2`. -/
theorem lt_hb {b : ℕ} (hb2 : 2 ≤ b) : b < hb b := by
  rw [hb_eq]; omega

/-- `h_b` is monotone in `b`. -/
theorem hb_mono : Monotone hb := fun _ _ h => Nat.add_le_add h (wb_mono h)

end CollatzPosDens
