/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Xo
public import CollatzPosDens.Transfer.S02Xl

/-!
# The total allowance `W`

For a Fourier index `ι ∈ 𝔍 = {o, b}` and `v ∈ ℕ` the total allowance is the rational number
`W(ι, v) = X_o(ι) + X_l(ι, v)`, the sum of the overshoot allowance `X_o(ι)` and the vertical
allowance `X_l(ι, v)`. Explicitly, `W(o, v) = 1697 + (6579/500) v` and
`W(b, v) = 1356 + (1653/125) v`.

## Main definitions

* `CollatzPosDens.totalAllowance`: the total allowance `W(ι, v) = X_o(ι) + X_l(ι, v) : ℚ`.

## Main results

* `CollatzPosDens.totalAllowance_def`: `W(ι, v) = X_o(ι) + X_l(ι, v)`.
* `CollatzPosDens.totalAllowance_apply_o`, `CollatzPosDens.totalAllowance_apply_b`:
  `W(o, v) = 1697 + η_dv(o) v` and `W(b, v) = 1356 + η_dv(b) v`.
* `CollatzPosDens.totalAllowance_eq_o`, `CollatzPosDens.totalAllowance_eq_b`: the explicit values.
* `CollatzPosDens.totalAllowance_cast_o`, `CollatzPosDens.totalAllowance_cast_b`: the explicit
  values cast into a division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.totalAllowance_pos`: `0 < W(ι, v)`.
* `CollatzPosDens.totalAllowance_succ`: `W(ι, v + 1) = W(ι, v) + η_dv(ι)`.
* `CollatzPosDens.totalAllowance_strictMono`: `W(ι, ·)` is strictly increasing.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The total allowance `W(ι, v) := X_o(ι) + X_l(ι, v) ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_Wtot"]
def totalAllowance (ι : FIndex) (v : ℕ) : ℚ := overshootAllowance ι + Xl ι v

/-- The total allowance is the sum of the overshoot and vertical allowances. -/
theorem totalAllowance_def (ι : FIndex) (v : ℕ) :
    totalAllowance ι v = overshootAllowance ι + Xl ι v := rfl

/-- The total allowance at the original index, in terms of the vertical deviation slope. -/
theorem totalAllowance_apply_o (v : ℕ) : totalAllowance .o v = 1697 + devEta .o * v := by
  rw [totalAllowance_def, cast_overshootAllowance_o, Xl_o, ← add_assoc]
  norm_num

/-- The total allowance at the bootstrap index, in terms of the vertical deviation slope. -/
theorem totalAllowance_apply_b (v : ℕ) : totalAllowance .b v = 1356 + devEta .b * v := by
  rw [totalAllowance_def, cast_overshootAllowance_b, Xl_b, ← add_assoc]
  norm_num

/-- The explicit value of the total allowance: `W(o, v) = 1697 + (6579/500) v`. -/
@[simp]
theorem totalAllowance_eq_o (v : ℕ) : totalAllowance .o v = 1697 + 6579 / 500 * (v : ℚ) := by
  rw [totalAllowance_apply_o, devEta_o]

/-- The explicit value of the total allowance: `W(b, v) = 1356 + (1653/125) v`. -/
@[simp]
theorem totalAllowance_eq_b (v : ℕ) : totalAllowance .b v = 1356 + 1653 / 125 * (v : ℚ) := by
  rw [totalAllowance_apply_b, devEta_b]

/-- The total allowance at the original index, cast into a division ring of characteristic
zero. -/
@[simp]
theorem totalAllowance_cast_o {K : Type*} [DivisionRing K] [CharZero K] (v : ℕ) :
    (totalAllowance .o v : K) = 1697 + 6579 / 500 * (v : K) := by
  rw [totalAllowance_apply_o, Rat.cast_add, Rat.cast_mul, devEta_cast_o, Rat.cast_natCast,
    Rat.cast_ofNat]

/-- The total allowance at the bootstrap index, cast into a division ring of characteristic
zero. -/
@[simp]
theorem totalAllowance_cast_b {K : Type*} [DivisionRing K] [CharZero K] (v : ℕ) :
    (totalAllowance .b v : K) = 1356 + 1653 / 125 * (v : K) := by
  rw [totalAllowance_apply_b, Rat.cast_add, Rat.cast_mul, devEta_cast_b, Rat.cast_natCast,
    Rat.cast_ofNat]

/-- The total allowance at `0` and the original index. -/
theorem totalAllowance_zero_o : totalAllowance .o 0 = 1697 := by
  simp

/-- The total allowance at `0` and the bootstrap index. -/
theorem totalAllowance_zero_b : totalAllowance .b 0 = 1356 := by
  simp

/-- The total allowance grows by `η_dv(ι)` per step. -/
theorem totalAllowance_succ (ι : FIndex) (v : ℕ) :
    totalAllowance ι (v + 1) = totalAllowance ι v + devEta ι := by
  rw [totalAllowance_def, totalAllowance_def, Xl_succ, add_assoc]

/-- The vertical allowance is at most the total allowance. -/
theorem Xl_le_totalAllowance (ι : FIndex) (v : ℕ) : Xl ι v ≤ totalAllowance ι v := by
  rw [totalAllowance_def]
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

/-- The overshoot allowance is at most the total allowance. -/
theorem overshootAllowance_le_totalAllowance (ι : FIndex) (v : ℕ) :
    (overshootAllowance ι : ℚ) ≤ totalAllowance ι v := by
  rw [totalAllowance_def]
  exact le_add_of_nonneg_right (Xl_pos ι v).le

/-- The total allowance is positive. -/
theorem totalAllowance_pos (ι : FIndex) (v : ℕ) : 0 < totalAllowance ι v :=
  lt_of_lt_of_le (Xl_pos ι v) (Xl_le_totalAllowance ι v)

/-- The total allowance is strictly increasing. -/
theorem totalAllowance_strictMono (ι : FIndex) : StrictMono (totalAllowance ι) := fun _ _ h => by
  simp only [totalAllowance_def, add_lt_add_iff_left]
  exact Xl_strictMono ι h

/-- The total allowance is monotone. -/
theorem totalAllowance_mono (ι : FIndex) : Monotone (totalAllowance ι) :=
  (totalAllowance_strictMono ι).monotone

end CollatzPosDens
