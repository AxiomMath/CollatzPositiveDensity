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
# The drift-free deviation slope `σ_dv`

For each Fourier index `ι ∈ 𝔍 = {o, b}` the drift-free deviation slope is a positive rational
constant `σ_dv(ι)`: `σ_dv(o) = 257/2000` and `σ_dv(b) = 383/2500`.

## Main definitions

* `CollatzPosDens.devSigma`: `σ_dv(ι) : ℚ` for `ι ∈ 𝔍 = {o, b}`, with `σ_dv(o) = 257 / 2000` and
  `σ_dv(b) = 383 / 2500`.

## Main results

* `CollatzPosDens.devSigma_o`, `CollatzPosDens.devSigma_b`: the two values.
* `CollatzPosDens.devSigma_cast_o`, `CollatzPosDens.devSigma_cast_b`: the two values cast into a
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.devSigma_pos`, `CollatzPosDens.devSigma_nonneg`: `σ_dv(ι)` is positive, hence
  nonnegative.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The drift-free deviation slope `σ_dv(ι) ∈ ℚ`: `σ_dv(o) := 257/2000` and
`σ_dv(b) := 383/2500`. -/
@[collatz_pos_dens "def_s02_dev_sigma"]
def devSigma : FIndex → ℚ
  | .o => 257 / 2000
  | .b => 383 / 2500

/-- The value of `σ_dv` at the original index `o`. -/
@[simp]
theorem devSigma_o : devSigma .o = 257 / 2000 := rfl

/-- The value of `σ_dv` at the bootstrap index `b`. -/
@[simp]
theorem devSigma_b : devSigma .b = 383 / 2500 := rfl

/-- The value of `σ_dv(o)` cast into a division ring of characteristic zero. -/
theorem devSigma_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (devSigma .o : K) = 257 / 2000 := by
  simp [devSigma_o]

/-- The value of `σ_dv(b)` cast into a division ring of characteristic zero. -/
theorem devSigma_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (devSigma .b : K) = 383 / 2500 := by
  simp [devSigma_b]

/-- `σ_dv(ι)` is positive. -/
theorem devSigma_pos (ι : FIndex) : 0 < devSigma ι := by
  cases ι <;> norm_num

/-- `σ_dv(ι)` is nonnegative. -/
theorem devSigma_nonneg (ι : FIndex) : 0 ≤ devSigma ι := (devSigma_pos ι).le

end CollatzPosDens
