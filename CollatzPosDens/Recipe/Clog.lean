/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr

/-!
# The binary ceiling logarithm `lg`

For a positive integer `u`, `lg u = ⌈log₂ u⌉` is the least natural number `e` with `u ≤ 2 ^ e`.
This is Mathlib's `Nat.clog 2`, and `lg` is a reducible abbreviation for it.

## Main definitions

* `CollatzPosDens.lg`: the binary ceiling logarithm `Nat.clog 2`.

## Main results

* `CollatzPosDens.le_two_pow_lg`: `u ≤ 2 ^ lg u`.
* `CollatzPosDens.lg_le_iff_le_two_pow`: `lg u ≤ e ↔ u ≤ 2 ^ e`.
* `CollatzPosDens.isLeast_lg`: `lg u` is the least `e` with `u ≤ 2 ^ e`.
* `CollatzPosDens.lg_eq_ceil_logb`: `lg u = ⌈log₂ u⌉`.

## Implementation notes

In [mazur2026] `lg` is defined on positive integers only. Here `lg` is defined on all of `ℕ`, with
`lg 0 = 0`; every characterization below holds without a positivity hypothesis, since `0` is also
the least `e` with `0 ≤ 2 ^ e`, and `⌈log₂ 0⌉ = 0` with Mathlib's convention `log 0 = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The binary ceiling logarithm `lg u = ⌈log₂ u⌉`, the least `e : ℕ` with `u ≤ 2 ^ e`. -/
@[collatz_pos_dens "def_s04_clog"]
abbrev lg (u : ℕ) : ℕ := Nat.clog 2 u

/-- `u ≤ 2 ^ lg u`. -/
theorem le_two_pow_lg (u : ℕ) : u ≤ 2 ^ lg u :=
  Nat.le_pow_clog (by norm_num) u

/-- `lg u ≤ e` exactly when `u ≤ 2 ^ e`. -/
theorem lg_le_iff_le_two_pow {u e : ℕ} : lg u ≤ e ↔ u ≤ 2 ^ e :=
  Nat.clog_le_iff_le_pow (by norm_num)

/-- Minimality of `lg`: if `u ≤ 2 ^ e` then `lg u ≤ e`. -/
theorem lg_le_of_le_two_pow {u e : ℕ} (h : u ≤ 2 ^ e) : lg u ≤ e :=
  lg_le_iff_le_two_pow.2 h

/-- `lg u` is the least natural number `e` with `u ≤ 2 ^ e`. -/
@[collatz_pos_dens "def_s04_clog"]
theorem isLeast_lg (u : ℕ) : IsLeast {e : ℕ | u ≤ 2 ^ e} (lg u) :=
  ⟨le_two_pow_lg u, fun _ he => lg_le_of_le_two_pow he⟩

/-- `lg u = ⌈log₂ u⌉`. -/
@[collatz_pos_dens "def_s04_clog"]
theorem lg_eq_ceil_logb (u : ℕ) : (lg u : ℤ) = ⌈Real.logb 2 u⌉ := by
  have := Real.ceil_logb_natCast (b := 2) (r := (u : ℝ)) (by positivity)
  push_cast at this
  rw [this, Int.clog_natCast]

end CollatzPosDens
