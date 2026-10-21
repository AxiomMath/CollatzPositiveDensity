/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The continuation factor `c_cont(ι)`

For each Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the continuation factor is the positive
rational constant `c_cont(ι)`, with `c_cont(o) = 14009206687631/500000000000` and
`c_cont(b) = 7245014059/500000000`.

## Main definitions

* `CollatzPosDens.ccont`: the continuation factor `c_cont(ι) : ℚ`.

## Main results

* `CollatzPosDens.ccont_o`, `CollatzPosDens.ccont_b`: the values of `c_cont(o)` and `c_cont(b)`.
* `CollatzPosDens.ccont_cast_o`, `CollatzPosDens.ccont_cast_b`: the same values cast into any
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.ccont_pos`: `0 < c_cont(ι)`.
* `CollatzPosDens.one_lt_ccont`: `1 < c_cont(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The continuation factor `c_cont(ι) ∈ ℚ` of the Fourier parameter set `ι`:
`c_cont(o) = 14009206687631/500000000000` and `c_cont(b) = 7245014059/500000000`. -/
@[collatz_pos_dens "def_s02_cont"]
def ccont : FIndex → ℚ
  | .o => 14009206687631 / 500000000000
  | .b => 7245014059 / 500000000

/-- The value of the continuation factor at the original index. -/
@[simp]
theorem ccont_o : ccont .o = 14009206687631 / 500000000000 := rfl

/-- The value of the continuation factor at the bootstrap index. -/
@[simp]
theorem ccont_b : ccont .b = 7245014059 / 500000000 := rfl

/-- The value of the continuation factor at the original index, cast into a division ring of
characteristic zero. -/
theorem ccont_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (ccont .o : K) = 14009206687631 / 500000000000 := by
  simp [ccont_o]

/-- The value of the continuation factor at the bootstrap index, cast into a division ring of
characteristic zero. -/
theorem ccont_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (ccont .b : K) = 7245014059 / 500000000 := by
  rw [ccont_b]; push_cast; rfl

/-- The continuation factor is positive. -/
theorem ccont_pos (ι : FIndex) : 0 < ccont ι := by
  cases ι <;> norm_num

/-- The continuation factor exceeds one. -/
theorem one_lt_ccont (ι : FIndex) : 1 < ccont ι := by
  cases ι <;> norm_num

end CollatzPosDens
