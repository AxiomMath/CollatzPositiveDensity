/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkExitWidth
public import CollatzPosDens.Transfer.EpsStar

/-!
# A clamped cap for raw three-crossings

For `s ∈ ℕ` this file defines the rational number
`ς_s = min {1, max {2^{-16}, (11/7) ε_* 9^{f_s} 2^{-s}}}`, where `ε_*` is the colour scale
`CollatzPosDens.epsStar` and `f_s` the exit width `CollatzPosDens.bkExitWidth`. The factor
`11/7` bounds `π/2`, so `(11/7) ε_* 9^{f_s} 2^{-s}` bounds the angle contribution of a raw
three-crossing; clamping it to `[2^{-16}, 1]` gives a coefficient that is always positive and
at most `1`.

## Main definitions

* `CollatzPosDens.trRaw3Cap`: the cap `ς_s`.

## Main results

* `CollatzPosDens.two_zpow_neg_sixteen_le_trRaw3Cap`, `CollatzPosDens.trRaw3Cap_le_one`:
  `2^{-16} ≤ ς_s ≤ 1`.
* `CollatzPosDens.trRaw3Cap_pos`: `0 < ς_s`.
* `CollatzPosDens.trRaw3Cap_le_max`: `ς_s ≤ max {2^{-16}, (11/7) ε_* 9^{f_s} 2^{-s}}`.
* `CollatzPosDens.trRaw3Cap_le_of_le`: `ς_s ≤ x` whenever `2^{-16} ≤ x` and
  `(11/7) ε_* 9^{f_s} 2^{-s} ≤ x`.

## References

* [Mazur, *Collatz positive density*], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The rational number
`ς_s := min {1, max {2^{-16}, (11/7) ε_* 9^{f_s} 2^{-s}}} ∈ ℚ`. -/
@[collatz_pos_dens "def_tr_raw3_cap"]
def trRaw3Cap (s : ℕ) : ℚ :=
  min 1 (max ((2 : ℚ) ^ (-16 : ℤ)) (11 / 7 * epsStar * 9 ^ bkExitWidth s * (2 : ℚ) ^ (-(s : ℤ))))

/-- Unfolding lemma for `trRaw3Cap`. -/
theorem trRaw3Cap_def (s : ℕ) :
    trRaw3Cap s = min 1 (max ((2 : ℚ) ^ (-16 : ℤ))
      (11 / 7 * epsStar * 9 ^ bkExitWidth s * (2 : ℚ) ^ (-(s : ℤ)))) := rfl

/-- The cap is at most `1`. -/
theorem trRaw3Cap_le_one (s : ℕ) : trRaw3Cap s ≤ 1 := min_le_left _ _

/-- The cap is at most `max {2^{-16}, (11/7) ε_* 9^{f_s} 2^{-s}}`. -/
theorem trRaw3Cap_le_max (s : ℕ) :
    trRaw3Cap s ≤ max ((2 : ℚ) ^ (-16 : ℤ))
      (11 / 7 * epsStar * 9 ^ bkExitWidth s * (2 : ℚ) ^ (-(s : ℤ))) := min_le_right _ _

/-- An upper bound for the cap from upper bounds for both terms of the inner maximum. -/
theorem trRaw3Cap_le_of_le {s : ℕ} {x : ℚ} (h₁ : (2 : ℚ) ^ (-16 : ℤ) ≤ x)
    (h₂ : 11 / 7 * epsStar * 9 ^ bkExitWidth s * (2 : ℚ) ^ (-(s : ℤ)) ≤ x) :
    trRaw3Cap s ≤ x :=
  (trRaw3Cap_le_max s).trans (max_le h₁ h₂)

/-- The cap is at least `2^{-16}`. -/
theorem two_zpow_neg_sixteen_le_trRaw3Cap (s : ℕ) : (2 : ℚ) ^ (-16 : ℤ) ≤ trRaw3Cap s :=
  le_min (zpow_le_one_of_nonpos₀ one_le_two (by norm_num)) (le_max_left _ _)

/-- The cap is positive. -/
theorem trRaw3Cap_pos (s : ℕ) : 0 < trRaw3Cap s :=
  (zpow_pos two_pos _).trans_le (two_zpow_neg_sixteen_le_trRaw3Cap s)

/-- The cap is nonnegative. -/
theorem trRaw3Cap_nonneg (s : ℕ) : 0 ≤ trRaw3Cap s := (trRaw3Cap_pos s).le

end CollatzPosDens
