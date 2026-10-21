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
# The packing numerators `C_i(ι)` of the trace schedule

For a Fourier index `ι ∈ 𝔍 = {o, b}` and `0 ≤ i < r_*(ι)`, the `i`-th packing numerator of the
trace schedule is the rational number
$$\mathsf C_i(\iota) := \tfrac{127}{40}\bigl(2\,\mathsf X_d(\iota, p_i(\iota)) + 1\bigr)
  + \mathsf W(\iota, p_i(\iota)),$$
where `p_i(ι)` is the `i`-th schedule position, `X_d(ι, ·)` the drift-free allowance and
`W(ι, ·)` the total allowance. Explicitly `C_i(o) = 101281/40 + (2137919/160000) p_i(o)` and
`C_i(b) = 16055/8 + (2693441/200000) p_i(b)`.

## Main definitions

* `CollatzPosDens.cStar`: the numerator `C_i(ι) = (127/40)(2 X_d(ι, p_i(ι)) + 1) + W(ι, p_i(ι))`.

## Main results

* `CollatzPosDens.cStar_def`: the defining formula.
* `CollatzPosDens.cStar_apply_o`, `CollatzPosDens.cStar_apply_b`: the explicit values.
* `CollatzPosDens.cStar_pos`: `0 < C_i(ι)`.
* `CollatzPosDens.cStar_strictMono`: `i ↦ C_i(ι)` is strictly increasing.

## Implementation notes

The numerators are only meaningful for `0 ≤ i < r_*(ι)` (`CollatzPosDens.rStar`). The definition
is total on `ℕ`, since `p_i`, `X_d` and `W` are; its values at `i ≥ r_*(ι)` are never used.
-/

@[expose] public section

namespace CollatzPosDens

/-- The packing numerators of the trace schedule:
`C_i(ι) := (127/40)(2 X_d(ι, p_i(ι)) + 1) + W(ι, p_i(ι)) ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_Ci"]
def cStar (ι : FIndex) (i : ℕ) : ℚ :=
  127 / 40 * (2 * Xd ι (schedule ι i) + 1) + totalAllowance ι (schedule ι i)

/-- The defining formula `C_i(ι) = (127/40)(2 X_d(ι, p_i(ι)) + 1) + W(ι, p_i(ι))`. -/
theorem cStar_def (ι : FIndex) (i : ℕ) :
    cStar ι i = 127 / 40 * (2 * Xd ι (schedule ι i) + 1) + totalAllowance ι (schedule ι i) :=
  rfl

/-- The explicit value `C_i(o) = 101281/40 + (2137919/160000) p_i(o)`. -/
theorem cStar_apply_o (i : ℕ) :
    cStar .o i = 101281 / 40 + 2137919 / 160000 * (schedule .o i : ℚ) := by
  rw [cStar_def, Xd_eq_o, totalAllowance_eq_o]
  ring

/-- The explicit value `C_i(b) = 16055/8 + (2693441/200000) p_i(b)`. -/
theorem cStar_apply_b (i : ℕ) :
    cStar .b i = 16055 / 8 + 2693441 / 200000 * (schedule .b i : ℚ) := by
  rw [cStar_def, Xd_eq_b, totalAllowance_eq_b]
  ring

/-- The packing numerators are positive. -/
theorem cStar_pos (ι : FIndex) (i : ℕ) : 0 < cStar ι i := by
  cases ι
  · rw [cStar_apply_o]; positivity
  · rw [cStar_apply_b]; positivity

/-- The packing numerators are strictly increasing in `i`. -/
theorem cStar_strictMono (ι : FIndex) : StrictMono (cStar ι) := fun a b h => by
  have : (schedule ι a : ℚ) < schedule ι b := by exact_mod_cast schedule_strictMono ι h
  cases ι
  · rw [cStar_apply_o, cStar_apply_o, add_lt_add_iff_left]; linarith
  · rw [cStar_apply_b, cStar_apply_b, add_lt_add_iff_left]; linarith

/-- The packing numerators are monotone in `i`. -/
theorem cStar_monotone (ι : FIndex) : Monotone (cStar ι) := (cStar_strictMono ι).monotone

end CollatzPosDens
