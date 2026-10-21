/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3RowTailExp

/-!
# Late tails of the raw-prefix rows

Let `ω ≥ 12500000` and `l` be integers with `ω - 127 ≤ l ≤ ω`. Then the masses
`CollatzPosDens.rawMass (r - 1) l` with `r > ⌊9ω/32⌋` sum to at most `37/ω`.

By `CollatzPosDens.sum_rawMass_late_tail_le_exp`, valid for `ω ≥ 680`, this sum is at most
`exp(-2ω/289)`. With `y = 2ω/289 ≥ 0` and `exp y ≥ y²/2`, this is at most
`2 · 289² / (4ω²) = 83521/(2ω²)`, which is at most `37/ω` as soon as `ω ≥ 1129`.

## Main results

* `CollatzPosDens.sum_rawMass_late_tail_le`: the late-tail bound, for every finite set of indices
  `r > ⌊9ω/32⌋`.

## Implementation notes

The sum over all integers `r > ⌊9ω/32⌋` has only finitely many nonzero terms, all of them
nonnegative, and `r - 1 ≥ 1` is a natural number. The bound is therefore stated for the sum over an
arbitrary finite set of natural numbers `r > ⌊9ω/32⌋`, which is equivalent to the bound on the
whole tail.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Finset Real

/-- For integers `ω ≥ 12500000` and `l` with `ω - 127 ≤ l ≤ ω`, and every finite set `s` of
indices `r > ⌊9ω/32⌋`, `∑ r ∈ s, rawMass (r - 1) l ≤ 37/ω`. -/
@[collatz_pos_dens "lem_c3_narrow_row"]
theorem sum_rawMass_late_tail_le {ω l : ℤ} (hω : 12500000 ≤ ω) (hl : ω - 127 ≤ l)
    (hlω : l ≤ ω) (s : Finset ℕ) (hs : ∀ r ∈ s, ⌊9 * (ω : ℝ) / 32⌋₊ < r) :
    ∑ r ∈ s, rawMass (r - 1) l ≤ 37 / (ω : ℝ) := by
  refine (sum_rawMass_late_tail_le_exp (by omega) hl hlω s hs).trans ?_
  have hw0 : (12500000 : ℝ) ≤ (ω : ℝ) := by exact_mod_cast hω
  have hy : 0 ≤ 2 * (ω : ℝ) / 289 := by positivity
  have h2 := quadratic_le_exp_of_nonneg hy
  rw [exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by positivity)]
  nlinarith

end CollatzPosDens
