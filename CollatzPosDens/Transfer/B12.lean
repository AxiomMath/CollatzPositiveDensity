/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rho
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The pair score `b_*`

The pair score is the rational number `b_* = ∑_{j=1}^{12} (1 - ϱ_*)^j / j`, the twelfth
partial sum of the series `-log ϱ_* = ∑_{j ≥ 1} (1 - ϱ_*)^j / j`, where `ϱ_*` is the
two-passage rate `CollatzPosDens.rhoStar`. Since `0 < 1 - ϱ_* < 1`, every term is positive, so
`0 < b_* < -log ϱ_*`.

## Main definitions

* `CollatzPosDens.bStar`: the pair score `b_* ∈ ℚ`.

## Main results

* `CollatzPosDens.bStar_def`: the defining sum over `j ∈ [1, 12]`.
* `CollatzPosDens.bStar_eq_sum_range`: the same sum re-indexed over `Finset.range 12`, in the
  form `∑_{i < 12} x^(i+1)/(i+1)` of the logarithm series.
* `CollatzPosDens.bStar_pos`: `0 < b_*`.

## Implementation notes

The constant is defined in `ℚ`; it is cast to `ℝ` where it is compared with the logarithm.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The pair score `b_* := ∑_{j=1}^{12} (1 - ϱ_*)^j / j ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_b12"]
def bStar : ℚ := ∑ j ∈ Finset.Icc (1 : ℕ) 12, (1 - rhoStar) ^ j / j

/-- The defining formula of the pair score. -/
theorem bStar_def : bStar = ∑ j ∈ Finset.Icc (1 : ℕ) 12, (1 - rhoStar) ^ j / j := rfl

/-- The pair score as the first twelve terms of the series `∑_{i} x^(i+1)/(i+1)`,
with `x = 1 - ϱ_*`. -/
theorem bStar_eq_sum_range :
    bStar = ∑ i ∈ Finset.range 12, (1 - rhoStar) ^ (i + 1) / (i + 1) := by
  have h : Finset.Icc (1 : ℕ) 12 = Finset.Ico (0 + 1) (12 + 1) := by decide
  rw [bStar_def, Finset.range_eq_Ico, h,
    ← Finset.sum_Ico_add' (fun j : ℕ => (1 - rhoStar) ^ j / j)]
  simp

/-- The pair score is positive. -/
theorem bStar_pos : 0 < bStar := by
  rw [bStar_def]
  have hx : 0 < 1 - rhoStar := sub_pos.mpr rhoStar_lt_one
  exact Finset.sum_pos (fun j hj => by
    have : (0 : ℚ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    exact div_pos (pow_pos hx j) this) ⟨1, by simp⟩

end CollatzPosDens
