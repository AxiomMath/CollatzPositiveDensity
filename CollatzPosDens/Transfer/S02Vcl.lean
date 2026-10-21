/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Alpha

/-!
# The clearing exponent `v_cl(ι)`

For each Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the clearing exponent is the rational constant
`v_cl(ι)`, with `v_cl(o) = 1279/100` and `v_cl(b) = 25/2`. It is the exponent of the clearing
point in the clearing estimate: the clearing generating function at `y_cl(ι)` is bounded by
`y_cl(ι) ^ v_cl(ι)`. Along the trace schedule of slope `α_sc(ι)` the clearing gain
`v_cl(ι) α_sc(ι)` beats the cost `13/9` of the stopping prefix:
`1279/100 · 113/1000 - 13/9 = 743/900000` and `25/2 · 3/25 - 13/9 = 1/18`.

## Main definitions

* `CollatzPosDens.clearingPower`: the clearing exponent `v_cl(ι) : ℚ`.

## Main results

* `CollatzPosDens.clearingPower_o`, `CollatzPosDens.clearingPower_b`: the values
  `v_cl(o) = 1279/100` and `v_cl(b) = 25/2`.
* `CollatzPosDens.clearingPower_cast_o`, `CollatzPosDens.clearingPower_cast_b`: the same values
  cast into any division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.clearingPower_pos`: `0 < v_cl(ι)`.
* `CollatzPosDens.clearingPower_mul_traceSlope_sub_o`,
  `CollatzPosDens.clearingPower_mul_traceSlope_sub_b`, and
  `CollatzPosDens.clearingPower_mul_traceSlope_sub_pos`: the margin `v_cl(ι) α_sc(ι) - 13/9`
  equals `743/900000` at `o` and `1/18` at `b`, hence is positive.

## Implementation notes

The constant `v_cl` is named `clearingPower` to keep it apart from
`CollatzPosDens.clearingExponent`, the per-interval clearing exponent `t^cl_i(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clearing exponent `v_cl(ι) ∈ ℚ` of the Fourier parameter set `ι`: `v_cl(o) = 1279/100`
and `v_cl(b) = 25/2`. -/
@[collatz_pos_dens "def_s02_vcl"]
def clearingPower : FIndex → ℚ
  | .o => 1279 / 100
  | .b => 25 / 2

/-- The clearing exponent at the original index. -/
@[simp]
theorem clearingPower_o : clearingPower .o = 1279 / 100 := rfl

/-- The clearing exponent at the bootstrap index. -/
@[simp]
theorem clearingPower_b : clearingPower .b = 25 / 2 := rfl

/-- The clearing exponent at the original index, cast into a division ring of characteristic
zero. -/
theorem clearingPower_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (clearingPower .o : K) = 1279 / 100 := by
  simp [clearingPower_o]

/-- The clearing exponent at the bootstrap index, cast into a division ring of characteristic
zero. -/
theorem clearingPower_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (clearingPower .b : K) = 25 / 2 := by
  simp [clearingPower_b]

/-- The clearing exponent is positive. -/
theorem clearingPower_pos (ι : FIndex) : 0 < clearingPower ι := by
  cases ι <;> norm_num

/-- At the original index, `v_cl(o) α_sc(o) - 13/9 = 743/900000`. -/
theorem clearingPower_mul_traceSlope_sub_o :
    clearingPower .o * traceSlope .o - 13 / 9 = 743 / 900000 := by
  norm_num

/-- At the bootstrap index, `v_cl(b) α_sc(b) - 13/9 = 1/18`. -/
theorem clearingPower_mul_traceSlope_sub_b :
    clearingPower .b * traceSlope .b - 13 / 9 = 1 / 18 := by
  norm_num

/-- Along the trace schedule the clearing gain beats the stopping cost:
`13/9 < v_cl(ι) α_sc(ι)`. -/
theorem clearingPower_mul_traceSlope_sub_pos (ι : FIndex) :
    0 < clearingPower ι * traceSlope ι - 13 / 9 := by
  cases ι <;> norm_num

end CollatzPosDens
