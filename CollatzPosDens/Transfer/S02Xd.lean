/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02DevSigma
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The drift-free allowance `X_d`

For a Fourier index `ι ∈ 𝔍 = {o, b}` and a horizon `v ∈ ℕ`, the drift-free allowance is the
rational number
$$X_d(o, v) := 131 + \frac{\sigma_{dv}(o)\, v}{4}, \qquad
  X_d(b, v) := 102 + \frac{\sigma_{dv}(b)\, v}{4},$$
where `σ_dv` is the drift-free deviation slope `devSigma`. It bounds the admissible drift
`|j_u - l_u / 4|` of the prefix sums of an atom along the first `v` steps.

## Main definitions

* `CollatzPosDens.Xd`: the drift-free allowance `X_d(ι, v) ∈ ℚ`.

## Main results

* `CollatzPosDens.Xd_o`, `CollatzPosDens.Xd_b`: the defining formulas at each index.
* `CollatzPosDens.Xd_eq_o`, `CollatzPosDens.Xd_eq_b`: the explicit formulas
  `X_d(o, v) = 131 + 257 v / 8000` and `X_d(b, v) = 102 + 383 v / 10000`.
* `CollatzPosDens.cast_Xd_o`, `CollatzPosDens.cast_Xd_b`: the defining formulas cast into a
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Xd_eq_Xd_zero_add`: `X_d(ι, v) = X_d(ι, 0) + σ_dv(ι) v / 4`.
* `CollatzPosDens.four_mul_Xd_o`, `CollatzPosDens.four_mul_Xd_b`: `4 X_d(o, v) = 524 + σ_dv(o) v`
  and `4 X_d(b, v) = 408 + σ_dv(b) v`.
* `CollatzPosDens.Xd_zero_le`, `CollatzPosDens.Xd_pos`, `CollatzPosDens.Xd_mono`:
  `X_d(ι, 0) ≤ X_d(ι, v)`, `0 < X_d(ι, v)`, and `X_d(ι, ·)` is monotone.

## Implementation notes

`X_d` takes values in `ℚ`, so that exact rational bounds on it can be stated; its casts to `ℝ`
are computed by `cast_Xd_o` and `cast_Xd_b`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The drift-free allowance `X_d(ι, v) ∈ ℚ`: `X_d(o, v) := 131 + σ_dv(o) v / 4` and
`X_d(b, v) := 102 + σ_dv(b) v / 4`, where `σ_dv` is `devSigma`. -/
@[collatz_pos_dens "def_s02_Xd"]
def Xd : FIndex → ℕ → ℚ
  | .o, v => 131 + devSigma .o * v / 4
  | .b, v => 102 + devSigma .b * v / 4

/-- The defining formula of `X_d` at the original index. -/
theorem Xd_o (v : ℕ) : Xd .o v = 131 + devSigma .o * v / 4 := rfl

/-- The defining formula of `X_d` at the bootstrap index. -/
theorem Xd_b (v : ℕ) : Xd .b v = 102 + devSigma .b * v / 4 := rfl

/-- The explicit formula `X_d(o, v) = 131 + 257 v / 8000`. -/
theorem Xd_eq_o (v : ℕ) : Xd .o v = 131 + 257 * (v : ℚ) / 8000 := by
  rw [Xd_o, devSigma_o]; ring

/-- The explicit formula `X_d(b, v) = 102 + 383 v / 10000`. -/
theorem Xd_eq_b (v : ℕ) : Xd .b v = 102 + 383 * (v : ℚ) / 10000 := by
  rw [Xd_b, devSigma_b]; ring

/-- The defining formula of `X_d(o, ·)`, cast into a division ring of characteristic zero. -/
theorem cast_Xd_o {K : Type*} [DivisionRing K] [CharZero K] (v : ℕ) :
    (Xd .o v : K) = 131 + (devSigma .o : K) * v / 4 := by
  rw [Xd_o]; push_cast; rfl

/-- The defining formula of `X_d(b, ·)`, cast into a division ring of characteristic zero. -/
theorem cast_Xd_b {K : Type*} [DivisionRing K] [CharZero K] (v : ℕ) :
    (Xd .b v : K) = 102 + (devSigma .b : K) * v / 4 := by
  rw [Xd_b]; push_cast; rfl

/-- `X_d(o, 0) = 131`. -/
@[simp] theorem Xd_zero_o : Xd .o 0 = 131 := by simp [Xd_o]

/-- `X_d(b, 0) = 102`. -/
@[simp] theorem Xd_zero_b : Xd .b 0 = 102 := by simp [Xd_b]

/-- The drift-free allowance is its value at `0` plus `σ_dv(ι) v / 4`. -/
theorem Xd_eq_Xd_zero_add (ι : FIndex) (v : ℕ) : Xd ι v = Xd ι 0 + devSigma ι * v / 4 := by
  cases ι
  · rw [Xd_zero_o, Xd_o]
  · rw [Xd_zero_b, Xd_b]

/-- `4 X_d(o, v) = 524 + σ_dv(o) v`. -/
theorem four_mul_Xd_o (v : ℕ) : 4 * Xd .o v = 524 + devSigma .o * v := by
  rw [Xd_o]; ring

/-- `4 X_d(b, v) = 408 + σ_dv(b) v`. -/
theorem four_mul_Xd_b (v : ℕ) : 4 * Xd .b v = 408 + devSigma .b * v := by
  rw [Xd_b]; ring

/-- `X_d(ι, 0) ≤ X_d(ι, v)`. -/
theorem Xd_zero_le (ι : FIndex) (v : ℕ) : Xd ι 0 ≤ Xd ι v := by
  rw [Xd_eq_Xd_zero_add ι v]
  have : (0 : ℚ) ≤ devSigma ι * v := mul_nonneg (devSigma_nonneg ι) v.cast_nonneg
  linarith

/-- `131 ≤ X_d(o, v)`. -/
theorem le_Xd_o (v : ℕ) : 131 ≤ Xd .o v := Xd_zero_o ▸ Xd_zero_le .o v

/-- `102 ≤ X_d(b, v)`. -/
theorem le_Xd_b (v : ℕ) : 102 ≤ Xd .b v := Xd_zero_b ▸ Xd_zero_le .b v

/-- `X_d(ι, v)` is positive. -/
theorem Xd_pos (ι : FIndex) (v : ℕ) : 0 < Xd ι v := by
  cases ι
  · exact lt_of_lt_of_le (by norm_num) (le_Xd_o v)
  · exact lt_of_lt_of_le (by norm_num) (le_Xd_b v)

/-- `X_d(ι, ·)` is monotone in the horizon. -/
theorem Xd_mono (ι : FIndex) : Monotone (Xd ι) := fun a b h => by
  rw [Xd_eq_Xd_zero_add ι a, Xd_eq_Xd_zero_add ι b]
  have : devSigma ι * (a : ℚ) ≤ devSigma ι * b :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast h) (devSigma_nonneg ι)
  linarith

end CollatzPosDens
