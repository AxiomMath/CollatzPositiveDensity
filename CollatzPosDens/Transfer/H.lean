/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Tactic.NormNum

/-!
# The plateau height `H_*`

This file defines the natural number `H_* = 17451`, the plateau height of stopping-time weights
of the form `β_*(q) = K_* (q + 1) 2^{max(0, bl(q+1) - H_*)}`, where `K_*` is a constant and
`bl` is binary length: below binary length `H_*` the weight is linear in `q + 1`, and above it
the weight doubles with each extra bit. The value `17451` is the binary length of the envelope
bound `1025 a_*^{580}`, so that `1025 a_*^{580} < 2^{H_*}`.

## Main definitions

* `CollatzPosDens.Hstar`: the plateau height `H_* = 17451 : ℕ`.

## Main results

* `CollatzPosDens.Hstar_def`: the value `H_* = 17451`.
* `CollatzPosDens.Hstar_cast`: the value of `(H_* : R)` in any additive monoid with one.
* `CollatzPosDens.Hstar_pos`: `0 < H_*`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The plateau height `H_* := 17451 ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_H"]
def Hstar : ℕ := 17451

/-- The value of the plateau height. -/
theorem Hstar_def : Hstar = 17451 := rfl

/-- The value of the plateau height cast into an additive monoid with one, e.g. `ℝ`. -/
@[simp]
theorem Hstar_cast {R : Type*} [AddMonoidWithOne R] : (Hstar : R) = 17451 := by
  rw [Hstar_def]; norm_num

/-- The plateau height is positive. -/
theorem Hstar_pos : 0 < Hstar := by
  rw [Hstar_def]; norm_num

end CollatzPosDens
