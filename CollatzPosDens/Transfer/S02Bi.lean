/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Schedule
public import CollatzPosDens.Transfer.S02Wtot
public import CollatzPosDens.Transfer.S02Xd

/-!
# The packing widths `B_i(ι)` of the trace schedule

For a Fourier index `ι ∈ 𝔍 = {o, b}` and `0 ≤ i < r_*(ι)`, the `i`-th packing width of the trace
schedule is the rational number
$$\mathsf B_i(\iota) := 2\,\mathsf X_{\mathrm d}(\iota, p_i(\iota))
  + \tfrac{8}{25}\,\mathsf W(\iota, p_i(\iota)) + 1,$$
where `p_i(ι)` is the `i`-th schedule position, `X_d(ι, ·)` the drift-free allowance and
`W(ι, ·)` the total allowance. Explicitly `B_i(o) = 20151/25 + (427481/100000) p_i(o)` and
`B_i(b) = 15973/25 + (107707/25000) p_i(b)`.

## Main definitions

* `CollatzPosDens.packWidth`: the packing width
  `B_i(ι) = 2 X_d(ι, p_i(ι)) + (8/25) W(ι, p_i(ι)) + 1 : ℚ`.

## Main results

* `CollatzPosDens.packWidth_def`: the defining formula.
* `CollatzPosDens.packWidth_eq_o`, `CollatzPosDens.packWidth_eq_b`: the explicit values.
* `CollatzPosDens.packWidth_cast_o`, `CollatzPosDens.packWidth_cast_b`: the explicit values cast
  into a division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.packWidth_pos`: `0 < B_i(ι)`.
* `CollatzPosDens.packWidth_strictMono`: `i ↦ B_i(ι)` is strictly increasing.

## Implementation notes

The widths are only meaningful for `0 ≤ i < r_*(ι)` (`CollatzPosDens.rStar`). The definition is
total on `ℕ`, since `p_i`, `X_d` and `W` are; its values at `i ≥ r_*(ι)` are never used.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The packing widths of the trace schedule:
`B_i(ι) := 2 X_d(ι, p_i(ι)) + (8/25) W(ι, p_i(ι)) + 1 ∈ ℚ` (used for `0 ≤ i < r_*(ι)`). -/
@[collatz_pos_dens "def_s02_Bi"]
def packWidth (ι : FIndex) (i : ℕ) : ℚ :=
  2 * Xd ι (schedule ι i) + 8 / 25 * totalAllowance ι (schedule ι i) + 1

/-- The defining formula `B_i(ι) = 2 X_d(ι, p_i(ι)) + (8/25) W(ι, p_i(ι)) + 1`. -/
theorem packWidth_def (ι : FIndex) (i : ℕ) :
    packWidth ι i = 2 * Xd ι (schedule ι i) + 8 / 25 * totalAllowance ι (schedule ι i) + 1 :=
  rfl

/-- The explicit value `B_i(o) = 20151/25 + (427481/100000) p_i(o)`. -/
theorem packWidth_eq_o (i : ℕ) :
    packWidth .o i = 20151 / 25 + 427481 / 100000 * (schedule .o i : ℚ) := by
  rw [packWidth_def, Xd_eq_o, totalAllowance_eq_o]
  ring

/-- The explicit value `B_i(b) = 15973/25 + (107707/25000) p_i(b)`. -/
theorem packWidth_eq_b (i : ℕ) :
    packWidth .b i = 15973 / 25 + 107707 / 25000 * (schedule .b i : ℚ) := by
  rw [packWidth_def, Xd_eq_b, totalAllowance_eq_b]
  ring

/-- The explicit value of `B_i(o)` cast into a division ring of characteristic zero. -/
theorem packWidth_cast_o {K : Type*} [DivisionRing K] [CharZero K] (i : ℕ) :
    (packWidth .o i : K) = 20151 / 25 + 427481 / 100000 * (schedule .o i : K) := by
  rw [packWidth_eq_o]
  push_cast
  rfl

/-- The explicit value of `B_i(b)` cast into a division ring of characteristic zero. -/
theorem packWidth_cast_b {K : Type*} [DivisionRing K] [CharZero K] (i : ℕ) :
    (packWidth .b i : K) = 15973 / 25 + 107707 / 25000 * (schedule .b i : K) := by
  rw [packWidth_eq_b]
  push_cast
  rfl

/-- The packing widths are positive. -/
theorem packWidth_pos (ι : FIndex) (i : ℕ) : 0 < packWidth ι i := by
  cases ι
  · rw [packWidth_eq_o]; positivity
  · rw [packWidth_eq_b]; positivity

/-- The packing widths are strictly increasing in `i`. -/
theorem packWidth_strictMono (ι : FIndex) : StrictMono (packWidth ι) := fun a b h => by
  have : (schedule ι a : ℚ) < schedule ι b := by exact_mod_cast schedule_strictMono ι h
  cases ι
  · simp only [packWidth_eq_o, add_lt_add_iff_left]; linarith
  · simp only [packWidth_eq_b, add_lt_add_iff_left]; linarith

/-- The packing widths are monotone in `i`. -/
theorem packWidth_mono (ι : FIndex) : Monotone (packWidth ι) :=
  (packWidth_strictMono ι).monotone

end CollatzPosDens
