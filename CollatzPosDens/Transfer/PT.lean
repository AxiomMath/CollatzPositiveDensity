/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.TraceReserve
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Rat.BigOperators

/-!
# The trace Taylor sum `P_T`

The trace Taylor sum is the rational number
`P_T = ∑_{j=0}^{50} L_*^j / j!`, the degree-`50` Taylor polynomial of the exponential evaluated at
the trace reserve `L_*`. Since `L_* > 0`, every term is positive, so `1 ≤ P_T`, and `P_T` is a
lower bound for `exp L_*`.

## Main definitions

* `CollatzPosDens.PT`: the trace Taylor sum `P_T = ∑_{j=0}^{50} L_*^j / j! : ℚ`.

## Main results

* `CollatzPosDens.PT_cast`: the cast of `P_T` to a division ring of characteristic zero is
  the same Taylor sum evaluated at the cast of `L_*`.
* `CollatzPosDens.one_le_PT`, `CollatzPosDens.PT_pos`: `1 ≤ P_T` and `0 < P_T`.
* `CollatzPosDens.PT_le_exp`: `(P_T : ℝ) ≤ exp L_*`.

## Implementation notes

The sum `∑_{j=0}^{50}` is written as a sum over `Finset.range 51`, matching the form of Mathlib's
`Real.sum_le_exp_of_nonneg`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The trace Taylor sum `P_T := ∑_{j=0}^{50} L_*^j / j! ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_PT"]
def PT : ℚ := ∑ j ∈ Finset.range 51, Lstar ^ j / j.factorial

/-- The trace Taylor sum equals `∑_{j=0}^{50} L_*^j / j!`. -/
theorem PT_def : PT = ∑ j ∈ Finset.range 51, Lstar ^ j / j.factorial := rfl

/-- The cast of the trace Taylor sum into a division ring of characteristic zero. -/
theorem PT_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (PT : K) = ∑ j ∈ Finset.range 51, (Lstar : K) ^ j / j.factorial := by
  simp only [PT_def, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

/-- The trace Taylor sum is at least `1` (its constant term). -/
theorem one_le_PT : 1 ≤ PT := by
  rw [PT_def, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, le_add_iff_nonneg_left]
  exact Finset.sum_nonneg fun j _ => by have := Lstar_pos; positivity

/-- The trace Taylor sum is positive. -/
theorem PT_pos : 0 < PT := zero_lt_one.trans_le one_le_PT

/-- The trace Taylor sum is a lower bound for `exp L_*`. -/
theorem PT_le_exp : (PT : ℝ) ≤ Real.exp Lstar := by
  rw [PT_cast]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast Lstar_pos.le) 51

end CollatzPosDens
