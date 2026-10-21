/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.SelEnd
public import CollatzPosDens.Seed.S05OffsetCap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith

/-!
# The loss from the offset cap

The offset cap `offsetCap = 2^600` is imposed on the `selEnd - 1 = 28` indices `i` with
`0 < i < selEnd`, and each such cap costs at most `7 / (offsetCap + 2)` of mass. The total loss
is tiny:
$$\sum_{0 < i < 29} \frac{7}{2^{600} + 2} = \frac{196}{2^{600} + 2}
  < \frac{256}{2^{600}} = 2^{-592}.$$

## Main results

* `CollatzPosDens.sum_seven_div_offsetCap_add_two_lt`:
  `∑_{0 < i < selEnd} 7 / (offsetCap + 2) < 2^{-592}`.

## Implementation notes

The index range `1 ≤ i ≤ selEnd - 1` is written as the open interval `Finset.Ioo 0 selEnd`.

## References

* [Mazur, *Collatz positive density*], §16.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- The total loss from the offset caps is tiny:
`∑_{0 < i < selEnd} 7 / (offsetCap + 2) < 2^{-592}`. -/
@[collatz_pos_dens "lem_s05_cap_loss"]
theorem sum_seven_div_offsetCap_add_two_lt :
    ∑ _i ∈ Finset.Ioo 0 selEnd, 7 / ((offsetCap : ℚ) + 2) < (2 : ℚ) ^ (-592 : ℤ) := by
  rw [Finset.sum_const, Nat.card_Ioo, selEnd_eq, nsmul_eq_mul, cast_offsetCap, zpow_neg,
    show (2 : ℚ) ^ (592 : ℤ) = 2 ^ 592 from zpow_natCast 2 592,
    show (2 : ℚ) ^ 600 = 2 ^ 8 * 2 ^ 592 by rw [← pow_add]]
  generalize hx : (2 : ℚ) ^ 592 = x
  have hx0 : 0 < x := hx ▸ by positivity
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ hx0]
  clear hx
  norm_num
  linarith

end CollatzPosDens
