/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02DevEta
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith

/-!
# The vertical allowance `X_l`

For a Fourier index `ι ∈ 𝔍 = {o, b}` and `v ∈ ℕ` the vertical allowance is the rational number
`X_l(o, v) = 1503 + η_dv(o) v` and `X_l(b, v) = 1174 + η_dv(b) v`, where `η_dv` is the vertical
deviation slope `CollatzPosDens.devEta`. It is the vertical summand of the total allowance
`W(ι, v) = X_o(ι) + X_l(ι, v)`.

## Main definitions

* `CollatzPosDens.Xl`: the vertical allowance `X_l(ι, v) : ℚ`.

## Main results

* `CollatzPosDens.Xl_o`, `CollatzPosDens.Xl_b`: the defining values at each index.
* `CollatzPosDens.Xl_eq_o`, `CollatzPosDens.Xl_eq_b`: the explicit values
  `X_l(o, v) = 1503 + (6579/500) v` and `X_l(b, v) = 1174 + (1653/125) v`.
* `CollatzPosDens.Xl_cast_o`, `CollatzPosDens.Xl_cast_b`: the explicit values cast into a
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Xl_eq_Xl_zero_add`: `X_l(ι, v) = X_l(ι, 0) + η_dv(ι) v`.
* `CollatzPosDens.Xl_pos`: `0 < X_l(ι, v)`.
* `CollatzPosDens.Xl_succ`: `X_l(ι, v + 1) = X_l(ι, v) + η_dv(ι)`.
* `CollatzPosDens.Xl_strictMono`: `X_l(ι, ·)` is strictly increasing.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The vertical allowance `X_l(ι, v) ∈ ℚ`: `X_l(o, v) := 1503 + η_dv(o) v` and
`X_l(b, v) := 1174 + η_dv(b) v`. -/
@[collatz_pos_dens "def_s02_Xl"]
def Xl : FIndex → ℕ → ℚ
  | .o, v => 1503 + devEta .o * v
  | .b, v => 1174 + devEta .b * v

/-- The vertical allowance at the original index, in terms of the vertical deviation slope. -/
theorem Xl_o (v : ℕ) : Xl .o v = 1503 + devEta .o * v := rfl

/-- The vertical allowance at the bootstrap index, in terms of the vertical deviation slope. -/
theorem Xl_b (v : ℕ) : Xl .b v = 1174 + devEta .b * v := rfl

/-- The explicit value of the vertical allowance at the original index. -/
@[simp]
theorem Xl_eq_o (v : ℕ) : Xl .o v = 1503 + 6579 / 500 * (v : ℚ) := by
  rw [Xl_o, devEta_o]

/-- The explicit value of the vertical allowance at the bootstrap index. -/
@[simp]
theorem Xl_eq_b (v : ℕ) : Xl .b v = 1174 + 1653 / 125 * (v : ℚ) := by
  rw [Xl_b, devEta_b]

/-- The vertical allowance at the original index, cast into a division ring of characteristic
zero. -/
@[simp]
theorem Xl_cast_o {K : Type*} [DivisionRing K] [CharZero K] (v : ℕ) :
    (Xl .o v : K) = 1503 + 6579 / 500 * (v : K) := by
  rw [Xl_o, Rat.cast_add, Rat.cast_mul, devEta_cast_o, Rat.cast_natCast, Rat.cast_ofNat]

/-- The vertical allowance at the bootstrap index, cast into a division ring of characteristic
zero. -/
@[simp]
theorem Xl_cast_b {K : Type*} [DivisionRing K] [CharZero K] (v : ℕ) :
    (Xl .b v : K) = 1174 + 1653 / 125 * (v : K) := by
  rw [Xl_b, Rat.cast_add, Rat.cast_mul, devEta_cast_b, Rat.cast_natCast, Rat.cast_ofNat]

/-- The vertical allowance at `0` and the original index. -/
theorem Xl_zero_o : Xl .o 0 = 1503 := by
  simp

/-- The vertical allowance at `0` and the bootstrap index. -/
theorem Xl_zero_b : Xl .b 0 = 1174 := by
  simp

/-- The vertical allowance is its value at `0` plus `η_dv(ι) v`. -/
theorem Xl_eq_Xl_zero_add (ι : FIndex) (v : ℕ) : Xl ι v = Xl ι 0 + devEta ι * v := by
  cases ι
  · rw [Xl_o, Xl_o 0, Nat.cast_zero, mul_zero, add_zero]
  · rw [Xl_b, Xl_b 0, Nat.cast_zero, mul_zero, add_zero]

/-- The vertical allowance is positive. -/
theorem Xl_pos (ι : FIndex) (v : ℕ) : 0 < Xl ι v := by
  have := devEta_nonneg ι
  cases ι
  · rw [Xl_o]; positivity
  · rw [Xl_b]; positivity

/-- The vertical allowance grows by `η_dv(ι)` per step. -/
theorem Xl_succ (ι : FIndex) (v : ℕ) : Xl ι (v + 1) = Xl ι v + devEta ι := by
  rw [Xl_eq_Xl_zero_add, Xl_eq_Xl_zero_add ι v, Nat.cast_succ, mul_add, mul_one, add_assoc]

/-- The vertical allowance is strictly increasing. -/
theorem Xl_strictMono (ι : FIndex) : StrictMono (Xl ι) := fun a b h => by
  rw [Xl_eq_Xl_zero_add ι a, Xl_eq_Xl_zero_add ι b, add_lt_add_iff_left]
  exact mul_lt_mul_of_pos_left (by exact_mod_cast h) (devEta_pos ι)

/-- The vertical allowance is monotone. -/
theorem Xl_mono (ι : FIndex) : Monotone (Xl ι) :=
  (Xl_strictMono ι).monotone

end CollatzPosDens
