/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The slope `α_sc(ι)` of the trace schedule

For each Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the slope of the trace schedule is the rational
constant `α_sc(ι)`, with `α_sc(o) = 113/1000` and `α_sc(b) = 3/25`.

## Main definitions

* `CollatzPosDens.traceSlope`: the slope `α_sc(ι) : ℚ` of the trace schedule.

## Main results

* `CollatzPosDens.traceSlope_o`, `CollatzPosDens.traceSlope_b`: the values `α_sc(o) = 113/1000`
  and `α_sc(b) = 3/25`.
* `CollatzPosDens.traceSlope_cast_o`, `CollatzPosDens.traceSlope_cast_b`: the same values cast
  into any division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.traceSlope_pos`, `CollatzPosDens.traceSlope_lt_one`: `0 < α_sc(ι) < 1`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The slope `α_sc(ι) ∈ ℚ` of the trace schedule of the Fourier parameter set `ι`:
`α_sc(o) = 113/1000` and `α_sc(b) = 3/25`. -/
@[collatz_pos_dens "def_s02_alpha"]
def traceSlope : FIndex → ℚ
  | .o => 113 / 1000
  | .b => 3 / 25

/-- The slope of the trace schedule at the original index. -/
@[simp]
theorem traceSlope_o : traceSlope .o = 113 / 1000 := rfl

/-- The slope of the trace schedule at the bootstrap index. -/
@[simp]
theorem traceSlope_b : traceSlope .b = 3 / 25 := rfl

/-- The slope of the trace schedule at the original index, cast into a division ring of
characteristic zero. -/
theorem traceSlope_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (traceSlope .o : K) = 113 / 1000 := by
  simp [traceSlope_o]

/-- The slope of the trace schedule at the bootstrap index, cast into a division ring of
characteristic zero. -/
theorem traceSlope_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (traceSlope .b : K) = 3 / 25 := by
  simp [traceSlope_b]

/-- The slope of the trace schedule is positive. -/
theorem traceSlope_pos (ι : FIndex) : 0 < traceSlope ι := by
  cases ι <;> norm_num

/-- The slope of the trace schedule is below `1`. -/
theorem traceSlope_lt_one (ι : FIndex) : traceSlope ι < 1 := by
  cases ι <;> norm_num

end CollatzPosDens
