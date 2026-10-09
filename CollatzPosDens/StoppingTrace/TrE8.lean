/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Tactic.Ring

/-!
# The eighth-order exponential defect

For real `t`, the *eighth-order exponential defect* is the alternating polynomial
`E₈(t) = ∑_{j=1}^{8} (-1)^{j+1} t^j / j!`. It is the degree-eight Taylor polynomial of
`1 - e^{-t}` at `0`; equivalently `1 - E₈(t) = ∑_{j=0}^{8} (-t)^j / j!` is the degree-eight
Taylor polynomial of `e^{-t}`. It is a polynomial with rational coefficients, so its value at a
rational point is the cast of a rational number.

## Main definitions

* `CollatzPosDens.E8`: the polynomial `E₈ : ℝ → ℝ`.
* `CollatzPosDens.E8Q`: the same polynomial over `ℚ`, used for exact rational evaluation.

## Main results

* `CollatzPosDens.E8_eq`: the expanded form
  `E₈(t) = t - t²/2 + t³/6 - t⁴/24 + t⁵/120 - t⁶/720 + t⁷/5040 - t⁸/40320`,
  suitable for exact evaluation by `norm_num`.
* `CollatzPosDens.one_sub_E8`: `1 - E₈(t) = ∑_{j=0}^{8} (-t)^j / j!`.
* `CollatzPosDens.E8_ratCast`: `E₈` at a rational point is the cast of the expanded rational
  polynomial; `CollatzPosDens.ratCast_E8Q` states the same in terms of `E8Q`.

## Implementation notes

`E8` is defined as a sum over `j ∈ [1, 8]`. Exact evaluations at rational constants are
obtained by rewriting with `E8_eq` (or `E8_ratCast`) and normalising.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The eighth-order exponential defect `E₈(t) = ∑_{j=1}^{8} (-1)^{j+1} t^j / j!`, the
degree-eight Taylor polynomial of `1 - e^{-t}`. -/
@[collatz_pos_dens "def_tr_E8"]
noncomputable def E8 (t : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 8, (-1) ^ (j + 1) * t ^ j / (j.factorial : ℝ)

/-- The expanded form of `E₈`. -/
theorem E8_eq (t : ℝ) :
    E8 t = t - t ^ 2 / 2 + t ^ 3 / 6 - t ^ 4 / 24 + t ^ 5 / 120 - t ^ 6 / 720
      + t ^ 7 / 5040 - t ^ 8 / 40320 := by
  simp [E8, Finset.sum_Icc_succ_top, Nat.factorial]
  ring

/-- `E₈` vanishes at `0`. -/
@[simp] theorem E8_zero : E8 0 = 0 := by
  simp [E8_eq]

/-- `1 - E₈(t)` is the degree-eight Taylor polynomial of `e^{-t}`. -/
theorem one_sub_E8 (t : ℝ) :
    1 - E8 t = ∑ j ∈ range 9, (-t) ^ j / (j.factorial : ℝ) := by
  simp [E8_eq, Finset.sum_range_succ, Nat.factorial]
  ring

/-- `E₈` as a polynomial over `ℚ`. -/
def E8Q (q : ℚ) : ℚ :=
  q - q ^ 2 / 2 + q ^ 3 / 6 - q ^ 4 / 24 + q ^ 5 / 120 - q ^ 6 / 720 + q ^ 7 / 5040 - q ^ 8 / 40320

/-- `E₈` at a rational point is the cast of the same polynomial evaluated in `ℚ`. -/
theorem E8_ratCast (q : ℚ) :
    E8 q = ((q - q ^ 2 / 2 + q ^ 3 / 6 - q ^ 4 / 24 + q ^ 5 / 120 - q ^ 6 / 720
      + q ^ 7 / 5040 - q ^ 8 / 40320 : ℚ) : ℝ) := by
  rw [E8_eq]
  push_cast
  ring

/-- The cast of `E8Q q` to `ℝ` is `E₈` evaluated at `q`. -/
theorem ratCast_E8Q (q : ℚ) : (E8Q q : ℝ) = E8 q :=
  (E8_ratCast q).symm

end CollatzPosDens
