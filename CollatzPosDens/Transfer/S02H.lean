/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Tactic.NormNum

/-!
# The window height `H_*(ι)`

This file defines the window height `H_*(ι) : ℕ`, which depends on the Fourier parameter index
`ι ∈ {o, b}`: `H_*(o) = 10100` and `H_*(b) = 500`. It is the additive part of the window length
`h_*(u) = ⌈α_sc β_*(u)⌉ + H_*` attached to a time `u`, where `α_sc(ι)` is the slope of the trace
schedule `(p_i)`, and it enters the increments of that schedule,
`p_{i+1} - p_i = ⌈α_sc K_{*,i} (p_i + 1)⌉ + H_* + T_* + 1`.

## Main definitions

* `CollatzPosDens.Hstar`: the window height `H_*(ι) : ℕ`.

## Main results

* `CollatzPosDens.Hstar_o`, `CollatzPosDens.Hstar_b`: `H_*(o) = 10100` and `H_*(b) = 500`.
* `CollatzPosDens.Hstar_o_cast`, `CollatzPosDens.Hstar_b_cast`: the values cast into a semiring.
* `CollatzPosDens.Hstar_pos`: `0 < H_*(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The window height `H_*(ι) ∈ ℕ`, equal to `10100` for `ι = o` and `500` for `ι = b`. -/
@[collatz_pos_dens "def_s02_H"]
def Hstar : FIndex → ℕ
  | .o => 10100
  | .b => 500

/-- The window height at the original index equals `10100`. -/
@[simp] theorem Hstar_o : Hstar .o = 10100 := rfl

/-- The window height at the bootstrap index equals `500`. -/
@[simp] theorem Hstar_b : Hstar .b = 500 := rfl

/-- The window height `H_*(o)` cast into a semiring, e.g. `ℝ`. -/
@[simp]
theorem Hstar_o_cast {R : Type*} [Semiring R] : (Hstar .o : R) = 10100 := by
  rw [Hstar_o, Nat.cast_ofNat]

/-- The window height `H_*(b)` cast into a semiring, e.g. `ℝ`. -/
@[simp]
theorem Hstar_b_cast {R : Type*} [Semiring R] : (Hstar .b : R) = 500 := by
  rw [Hstar_b, Nat.cast_ofNat]

/-- The window height is positive. -/
theorem Hstar_pos (ι : FIndex) : 0 < Hstar ι := by
  cases ι <;> decide

end CollatzPosDens
