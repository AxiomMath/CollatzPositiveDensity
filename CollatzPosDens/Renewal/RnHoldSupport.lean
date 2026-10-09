/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHold

/-!
# Support of the holding-time law

Write `η(j, l) = CollatzPosDens.holdLaw j l` for the holding-time law and
`𝒞_{j,l} = CollatzPosDens.holdWords j l` for the set of hold words. If `j ≥ 1` and
`η(j, l) ≠ 0`, then `l ≥ 2j + 2`. Indeed some term of the sum defining `η(j, l)` is nonzero, so
`𝒞_{j,l}` contains a word `c`. Its letters are at least `2` and its last letter lies in `{4, 5}`,
so `l = c₁ + ⋯ + c_j ≥ 2(j - 1) + 4 = 2j + 2`.

## Main results

* `CollatzPosDens.holdWords_nonempty_of_holdLaw_ne_zero`: `η(j, l) ≠ 0` forces `𝒞_{j,l}`
  to be nonempty.
* `CollatzPosDens.two_mul_add_two_le_of_holdLaw_ne_zero`: the support bound `l ≥ 2j + 2`
  for `j ≥ 1`.

## Implementation notes

The hypothesis that `(j, l)` lies in `CollatzPosDens.bkPoints` is stated as `1 ≤ j`, with
`j : ℕ` and `l : ℤ` as in `holdLaw`. It cannot be dropped: `η(0, 0) = 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `holdLaw j l ≠ 0` then the set of hold words `holdWords j l` is nonempty. -/
theorem holdWords_nonempty_of_holdLaw_ne_zero {j : ℕ} {l : ℤ} (h : holdLaw j l ≠ 0) :
    (holdWords j l).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  apply h
  rw [holdLaw_def]
  have : IsEmpty (holdWords j l) := by rw [hne]; infer_instance
  exact tsum_empty

/-- Support of the holding-time law: if `1 ≤ j` and `holdLaw j l ≠ 0`, then `2j + 2 ≤ l`. -/
@[collatz_pos_dens "lem_rn_hold_support"]
theorem two_mul_add_two_le_of_holdLaw_ne_zero {j : ℕ} {l : ℤ} (hj : 1 ≤ j)
    (h : holdLaw j l ≠ 0) : 2 * (j : ℤ) + 2 ≤ l := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨c, hc⟩ := holdWords_nonempty_of_holdLaw_ne_zero h
  have := holdWords_two_mul_add_two_le hc
  push_cast
  linarith

end CollatzPosDens
