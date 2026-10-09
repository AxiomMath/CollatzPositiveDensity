/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr

/-!
# The crossing level `Lv_n`

For an integer `n ≥ 1` this file defines the real number
$$\mathrm{Lv}_n = n \log_2 3 - \tfrac{9217}{4096} \log_2 n - 2.$$

## Main definitions

* `CollatzPosDens.mxLevel`: the crossing level `Lv_n`.

## Main results

* `CollatzPosDens.mxLevel_def`: the defining formula.
* `CollatzPosDens.mxLevel_eq_logb`: `Lv_n = log₂ (3 ^ n) - (9217/4096) log₂ n - 2`.
* `CollatzPosDens.mxLevel_one`: `Lv_1 = log₂ 3 - 2`.
* `CollatzPosDens.mxLevel_zero`: the junk value `Lv_0 = -2`.

## Implementation notes

The definition is stated for every natural number `n`; at `n = 0` it takes the junk value `-2`
(since `Real.logb 2 0 = 0`), and the hypothesis `n ≥ 1` is carried by the lemmas that need it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The crossing level `Lv_n = n log₂ 3 - (9217/4096) log₂ n - 2`, meaningful for `n ≥ 1`. -/
@[collatz_pos_dens "def_mx_level"]
noncomputable def mxLevel (n : ℕ) : ℝ :=
  n * Real.logb 2 3 - 9217 / 4096 * Real.logb 2 n - 2

/-- The defining formula of `mxLevel`. -/
theorem mxLevel_def (n : ℕ) :
    mxLevel n = n * Real.logb 2 3 - 9217 / 4096 * Real.logb 2 n - 2 := rfl

/-- The level written with a single base-two logarithm of `3 ^ n`. -/
theorem mxLevel_eq_logb (n : ℕ) :
    mxLevel n = Real.logb 2 ((3 : ℝ) ^ n) - 9217 / 4096 * Real.logb 2 n - 2 := by
  rw [mxLevel_def, Real.logb_pow]

/-- The level at `n = 1` is `log₂ 3 - 2`. -/
@[simp]
theorem mxLevel_one : mxLevel 1 = Real.logb 2 3 - 2 := by
  simp [mxLevel_def]

/-- The level at `n = 0` is the junk value `-2`. -/
@[simp]
theorem mxLevel_zero : mxLevel 0 = -2 := by
  simp [mxLevel_def]

end CollatzPosDens
