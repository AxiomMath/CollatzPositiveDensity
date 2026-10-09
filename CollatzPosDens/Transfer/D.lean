/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The single-passage loss `d_*`

The single-passage loss is the rational constant
`d_* = (3/16) E_8(γ_*) + (1/4) E_8(κ_* γ_*)`, where
`E_8(x) = ∑_{j=1}^{8} (-1)^{j+1} x^j / j!` is the degree-eight truncation of `1 - exp (-x)`.
Here `γ_* = 87/200` is the trace tilt `CollatzPosDens.gammaStar` and `κ_* = 4/25` the
second-letter tilt ratio `CollatzPosDens.kappaStar`.

## Main definitions

* `CollatzPosDens.dStar`: the single-passage loss `d_* ∈ ℚ`.

## Main results

* `CollatzPosDens.dStar_eq`: the exact value
  `d_* = 331784646551677809785190276273027 / 4000000000000000000000000000000000`.
* `CollatzPosDens.dStar_pos`, `CollatzPosDens.dStar_lt_one`: `0 < d_* < 1`.

## Implementation notes

The constant is defined in `ℚ`, with both truncated sums written over `Finset.Icc 1 8`, so that
downstream inequalities can be decided by `norm_num` from the closed-form value `dStar_eq`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The single-passage loss
`d_* := (3/16) ∑_{j=1}^{8} (-1)^{j+1} γ_*^j / j!`
`+ (1/4) ∑_{j=1}^{8} (-1)^{j+1} (κ_* γ_*)^j / j!`. -/
@[collatz_pos_dens "def_s02_d"]
def dStar : ℚ :=
  3 / 16 * ∑ j ∈ Icc 1 8, (-1) ^ (j + 1) * gammaStar ^ j / (j.factorial : ℚ) +
    1 / 4 * ∑ j ∈ Icc 1 8, (-1) ^ (j + 1) * (kappaStar * gammaStar) ^ j / (j.factorial : ℚ)

/-- The exact value of the single-passage loss. -/
@[simp]
theorem dStar_eq :
    dStar = 331784646551677809785190276273027 / 4000000000000000000000000000000000 := by
  rw [dStar, gammaStar_eq, kappaStar_def]
  rw [show Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} by decide]
  simp [Nat.factorial]
  norm_num

/-- The single-passage loss is positive. -/
theorem dStar_pos : 0 < dStar := by
  rw [dStar_eq]; norm_num

/-- The single-passage loss is less than one. -/
theorem dStar_lt_one : dStar < 1 := by
  rw [dStar_eq]; norm_num

end CollatzPosDens
