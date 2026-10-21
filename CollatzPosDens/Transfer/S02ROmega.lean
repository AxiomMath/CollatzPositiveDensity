/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02B
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor

/-!
# The far-gap scale `R_Ω`

The far-gap scale of the transfer argument at the Fourier parameter index `ι ∈ {o, b}` is the
natural number
$$R_Ω(o) := \lceil (1231/4) V_*(o) \rceil, \qquad R_Ω(b) := 45\, V_*(b),$$
where `V_*(ι)` is the active packing bound; at `o` the ceiling is that of the whole rational
product. Since `V_*(o)` is a natural number, `R_Ω(o)` is the integer `⌊(1231 V_*(o) + 3) / 4⌋`,
and it satisfies `(1231/4) V_*(o) ≤ R_Ω(o) < (1231/4) V_*(o) + 1`. At every index
`V_*(ι) ≤ R_Ω(ι)`.

## Main definitions

* `CollatzPosDens.ROmega`: the far-gap scale `R_Ω(ι)`.

## Main results

* `CollatzPosDens.ROmega_o`, `CollatzPosDens.ROmega_b`: the defining formulas
  `R_Ω(o) = ⌈(1231/4) V_*(o)⌉` and `R_Ω(b) = 45 V_*(b)`.
* `CollatzPosDens.ROmega_o_eq_div`: `R_Ω(o) = (1231 V_*(o) + 3) / 4` in natural-number division.
* `CollatzPosDens.le_ROmega_o`: `(1231/4) V_*(o) ≤ R_Ω(o)` in any linearly ordered field.
* `CollatzPosDens.ROmega_o_lt`: `R_Ω(o) < (1231/4) V_*(o) + 1` in any linearly ordered field.
* `CollatzPosDens.Vstar_le_ROmega`: `V_*(ι) ≤ R_Ω(ι)`.
* `CollatzPosDens.ROmega_pos`: `0 < R_Ω(ι)`.

## Implementation notes

The ceiling is taken over `ℚ`, where the product `(1231/4) V_*(o)` is exact; the comparison
lemmas transfer it to any linearly ordered field such as `ℝ`. `V_*(ι)` is a closed natural
number of many bits, so `R_Ω` is used through `ROmega_o`, `ROmega_b` and `ROmega_o_eq_div`
rather than by evaluation.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The far-gap scale `R_Ω(ι) ∈ ℕ`: `R_Ω(o) := ⌈(1231/4) V_*(o)⌉`, the ceiling of the whole
rational product, and `R_Ω(b) := 45 V_*(b)`. -/
@[collatz_pos_dens "def_s02_ROmega"]
noncomputable def ROmega : FIndex → ℕ
  | .o => ⌈(1231 / 4 : ℚ) * Vstar .o⌉₊
  | .b => 45 * Vstar .b

/-- The defining formula of `R_Ω(o)`. -/
theorem ROmega_o : ROmega .o = ⌈(1231 / 4 : ℚ) * Vstar .o⌉₊ := rfl

/-- The defining formula of `R_Ω(b)`. -/
theorem ROmega_b : ROmega .b = 45 * Vstar .b := rfl

/-- `R_Ω(o)` in natural-number arithmetic: `R_Ω(o) = (1231 V_*(o) + 3) / 4`. -/
theorem ROmega_o_eq_div : ROmega .o = (1231 * Vstar .o + 3) / 4 := by
  have hV := Vstar_pos .o
  rw [ROmega_o, Nat.ceil_eq_iff (by omega)]
  have h1 := Nat.div_add_mod (1231 * Vstar .o + 3) 4
  have h2 := Nat.mod_lt (1231 * Vstar .o + 3) (by norm_num : 0 < 4)
  set q := (1231 * Vstar .o + 3) / 4
  set r := (1231 * Vstar .o + 3) % 4
  have hq : 1 ≤ q := by omega
  have h1' : (4 : ℚ) * q + r = 1231 * Vstar .o + 3 := by exact_mod_cast h1
  have h2' : (r : ℚ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ h2
  have h3' : (0 : ℚ) ≤ r := r.cast_nonneg
  rw [Nat.cast_sub hq, Nat.cast_one]
  constructor <;> linarith

/-- The defining property of `R_Ω(o)` as an upper ceiling: `(1231/4) V_*(o) ≤ R_Ω(o)`. -/
theorem le_ROmega_o {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (1231 / 4 : K) * Vstar .o ≤ ROmega .o := by
  have h : (1231 / 4 : ℚ) * Vstar .o ≤ ROmega .o := by rw [ROmega_o]; exact Nat.le_ceil _
  have h' : ((1231 * Vstar .o : ℕ) : ℚ) ≤ ((4 * ROmega .o : ℕ) : ℚ) := by push_cast; linarith
  have h'' : ((1231 * Vstar .o : ℕ) : K) ≤ ((4 * ROmega .o : ℕ) : K) := by
    exact_mod_cast (Nat.cast_le.mp h')
  push_cast at h''
  linarith

/-- `R_Ω(o)` exceeds `(1231/4) V_*(o)` by less than one. -/
theorem ROmega_o_lt {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (ROmega .o : K) < (1231 / 4 : K) * Vstar .o + 1 := by
  have h : 4 * ROmega .o < 1231 * Vstar .o + 4 := by rw [ROmega_o_eq_div]; omega
  have h' : ((4 * ROmega .o : ℕ) : K) < ((1231 * Vstar .o + 4 : ℕ) : K) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- The far-gap scale dominates the active packing bound: `V_*(ι) ≤ R_Ω(ι)`. -/
theorem Vstar_le_ROmega (ι : FIndex) : Vstar ι ≤ ROmega ι := by
  cases ι
  · rw [ROmega_o_eq_div]
    omega
  · rw [ROmega_b]
    omega

/-- `R_Ω(ι)` is positive. -/
theorem ROmega_pos (ι : FIndex) : 0 < ROmega ι :=
  (Vstar_pos ι).trans_le (Vstar_le_ROmega ι)

end CollatzPosDens
