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
# The packing expansion length `H_pk`

For each Fourier parameter index `ι : CollatzPosDens.FIndex` this file defines a natural number
`H_pk(ι)`, the common expansion length of the packing intervals: `H_pk(o) = 35` and
`H_pk(b) = 33`.

## Main definitions

* `CollatzPosDens.Hpack`: the packing expansion length `H_pk(ι) : ℕ`.

## Main results

* `CollatzPosDens.Hpack_o`, `CollatzPosDens.Hpack_b`: `H_pk(o) = 35` and `H_pk(b) = 33`.
* `CollatzPosDens.Hpack_cast_o`, `CollatzPosDens.Hpack_cast_b`: the two values cast into a
  semiring.
* `CollatzPosDens.Hpack_pos`: `0 < H_pk(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The packing expansion length `H_pk(ι) ∈ ℕ`, the common expansion length of the packing
intervals: `H_pk(o) := 35` and `H_pk(b) := 33`. -/
@[collatz_pos_dens "def_s02_Hpack"]
def Hpack : FIndex → ℕ
  | .o => 35
  | .b => 33

/-- The packing expansion length at the original index. -/
@[simp]
theorem Hpack_o : Hpack .o = 35 := rfl

/-- The packing expansion length at the bootstrap index. -/
@[simp]
theorem Hpack_b : Hpack .b = 33 := rfl

/-- The packing expansion length `H_pk(o)` cast into a semiring, e.g. `ℝ`. -/
@[simp]
theorem Hpack_cast_o {R : Type*} [Semiring R] : (Hpack .o : R) = 35 := by
  rw [Hpack_o, Nat.cast_ofNat]

/-- The packing expansion length `H_pk(b)` cast into a semiring, e.g. `ℝ`. -/
@[simp]
theorem Hpack_cast_b {R : Type*} [Semiring R] : (Hpack .b : R) = 33 := by
  rw [Hpack_b, Nat.cast_ofNat]

/-- The packing expansion length is positive. -/
theorem Hpack_pos (ι : FIndex) : 0 < Hpack ι := by
  cases ι <;> decide

end CollatzPosDens
