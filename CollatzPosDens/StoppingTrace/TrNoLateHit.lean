/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrPathGrowthJ

/-!
# No black point beyond the strip

Let `o : ℤ × ℤ`, let `β : List (List ℤ × ℤ)` be a list of blocks, let `J : ℤ` and `t : ℕ`. If
`J < bkJ o + β.length` and `bkJ (trPath o β t) ≤ J`, then `bkJ o + t ≤ J`. Indeed the path
`trPath o β` grows in the `bkJ` coordinate by at least one per block read, so
`bkJ (trPath o β t) ≥ bkJ o + min t β.length`. If `t ≥ β.length` this is at least
`bkJ o + β.length > J`, which is impossible; hence `t < β.length` and
`bkJ o + t ≤ bkJ (trPath o β t) ≤ J`.

## Main results

* `CollatzPosDens.bkJ_add_le_of_bkJ_trPath_le`: if `J < bkJ o + β.length` and
  `bkJ (trPath o β t) ≤ J`, then `bkJ o + t ≤ J`.

## Implementation notes

In the source `J = ⌊n/2⌋`; the argument works for every integer `J`, so `J : ℤ` is arbitrary.
No restriction on the base point `o` or on the closing letters of the blocks is used, so the
statement holds for every `o : ℤ × ℤ` and every `β : List (List ℤ × ℤ)`.

## References

* [Mazur, *Collatz positive density*], §9.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `J < bkJ o + β.length` and `bkJ (trPath o β t) ≤ J`, then `bkJ o + t ≤ J`. -/
@[collatz_pos_dens "lem_tr_no_late_hit"]
theorem bkJ_add_le_of_bkJ_trPath_le {J : ℤ} (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) {t : ℕ}
    (hN : J < bkJ o + β.length) (ht : bkJ (trPath o β t) ≤ J) : bkJ o + t ≤ J := by
  have h := trPath_bkJ_sub_bkJ_ge o β (Nat.zero_le t)
  simp only [trPath_zero, Nat.zero_min, Nat.cast_zero, sub_zero] at h
  rcases le_total t β.length with h' | h'
  · rw [min_eq_left h'] at h
    omega
  · rw [min_eq_right h'] at h
    omega

end CollatzPosDens
