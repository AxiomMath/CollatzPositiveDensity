/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Positivity

/-!
# Rounded offsets

For a word `v = (a₁, …, a_d)` and an integer `p`, the *rounded offset* is the dyadic rational
$$\mathrm{rd}_p(v) = 2^{-p}\sum_{i=1}^{d}
  \Bigl\lceil 2^{p}\,3^{i-1}\,2^{-(a_1+\cdots+a_i)}\Bigr\rceil,$$
obtained from the offset sum `off v = ∑ᵢ 3^{i-1} 2^{-(a₁+⋯+aᵢ)}` by rounding every term up to
the grid `2^{-p} ℤ`. It is an exact rational number, so inequalities between rounded offsets and
explicit rationals can be decided by computation, while each rounded offset brackets the true
offset to within `|v| 2^{-p}`.

## Main definitions

* `CollatzPosDens.roundedOffset p v`: the rounded offset `rd_p(v) ∈ ℚ`.

## Main results

* `CollatzPosDens.roundedOffset_nil`: `rd_p(∅) = 0`.
* `CollatzPosDens.roundedOffset_nonneg`: `0 ≤ rd_p(v)`.

## Implementation notes

The sum is indexed by `j = i - 1 ∈ {0, …, d - 1}`, and the partial sum `a₁ + ⋯ + a_{j+1}` is
the sum of the prefix `v.take (j + 1)`, matching the closed form of the offset in
`CollatzPosDens.off_eq_sum`. The power `2^p` with `p ∈ ℤ` is a `zpow` in `ℚ`.

## References

* [Mazur, *Collatz positive density*], §17.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The rounded offset `rd_p(v) = 2^{-p} ∑_{i=1}^{d} ⌈2^p 3^{i-1} 2^{-(a₁+⋯+aᵢ)}⌉` of a word
`v = (a₁, …, a_d)` at precision `p ∈ ℤ`; the index `j = i - 1` runs over `range d`. -/
@[collatz_pos_dens "def_s05_rounded_offset"]
def roundedOffset (p : ℤ) (v : Word) : ℚ :=
  (2 : ℚ) ^ (-p) * ∑ j ∈ Finset.range v.length,
    ((⌈(2 : ℚ) ^ p * 3 ^ j * ((2 : ℚ) ^ Word.valSum (v.take (j + 1)))⁻¹⌉ : ℤ) : ℚ)

/-- The rounded offset of the empty word is `0`. -/
@[simp]
theorem roundedOffset_nil (p : ℤ) : roundedOffset p [] = 0 := by
  simp [roundedOffset]

/-- Rounded offsets are nonnegative. -/
theorem roundedOffset_nonneg (p : ℤ) (v : Word) : 0 ≤ roundedOffset p v := by
  unfold roundedOffset
  refine mul_nonneg (zpow_nonneg zero_le_two _) (Finset.sum_nonneg fun j _ => ?_)
  exact_mod_cast Int.ceil_nonneg
    (mul_nonneg (mul_nonneg (zpow_nonneg zero_le_two _) (by positivity)) (by positivity))

end CollatzPosDens
