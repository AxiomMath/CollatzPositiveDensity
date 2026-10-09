/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.GroupTheory.Index
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Reduction

/-!
# Averages over the fibres of a residue reduction

For `0 ≤ m ≤ n`, a function `c : G_n → ℝ` and `y ∈ G_n`, the fibre average of `c` at `y` is
`Avg_{m,n} c (y) = 3^{m-n} ∑_{y' ∈ G_n, π_{n,m} y' = π_{n,m} y} c y'`,
the uniform average of `c` over the fibre of the reduction `π_{n,m} : G_n → G_m` through `y`.
Every such fibre has exactly `3^{n-m}` elements, so this is a genuine average: it fixes
constants, it is constant along fibres, and it preserves the total average `⟨c⟩_n`.

## Main definitions

* `CollatzPosDens.fiberAvg h c y`: for `h : m ≤ n`, the fibre average `Avg_{m,n} c (y)`.

## Main results

* `CollatzPosDens.fiberAvg_const`: the fibre average of a constant is that constant.
* `CollatzPosDens.fiberAvg_self`: `Avg_{n,n} c = c`.
* `CollatzPosDens.fiberAvg_eq_of_residueReduction_eq`: `Avg_{m,n} c` is constant on fibres.
* `CollatzPosDens.residueAvg_fiberAvg`: `⟨Avg_{m,n} c⟩_n = ⟨c⟩_n`.

## Implementation notes

The hypothesis `m ≤ n` is taken as an explicit proof argument, since the reduction
`π_{n,m}` it uses is only defined for `m ≤ n`.

## References

* [Mazur, *Collatz positive density*], §13.1.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `h : m ≤ n`, the average of `c : G_n → ℝ` over the fibre of `π_{n,m}` through `y`:
`Avg_{m,n} c (y) = 3^{m-n} ∑_{y' ∈ G_n, π_{n,m} y' = π_{n,m} y} c y'`. -/
@[collatz_pos_dens "def_mx_fiber_avg"]
noncomputable def fiberAvg {m n : ℕ} (h : m ≤ n) (c : ResidueGroup n → ℝ)
    (y : ResidueGroup n) : ℝ :=
  (3 : ℝ) ^ ((m : ℤ) - n) *
    ∑ y' ∈ univ.filter (fun y' => residueReduction h y' = residueReduction h y), c y'

/-- The scaling factor `3^{m-n}` is the reciprocal of the fibre size `3^{n-m}`. -/
theorem three_zpow_sub_eq_inv {m n : ℕ} (h : m ≤ n) :
    (3 : ℝ) ^ ((m : ℤ) - n) = ((3 : ℝ) ^ (n - m))⁻¹ := by
  rw [← zpow_natCast, ← zpow_neg, Nat.cast_sub h, neg_sub]

/-- The fibre average of a constant function is that constant. -/
@[simp]
theorem fiberAvg_const {m n : ℕ} (h : m ≤ n) (a : ℝ) (y : ResidueGroup n) :
    fiberAvg h (fun _ => a) y = a := by
  rw [fiberAvg, sum_const, card_filter_residueReduction_eq, nsmul_eq_mul, three_zpow_sub_eq_inv h]
  push_cast
  field_simp

/-- The fibre average for `m = n` is the function itself. -/
@[simp]
theorem fiberAvg_self {n : ℕ} (c : ResidueGroup n → ℝ) (y : ResidueGroup n) :
    fiberAvg (le_refl n) c y = c y := by
  simp [fiberAvg, residueReduction_self, filter_eq']

/-- The fibre average is constant along the fibres of `π_{n,m}`. -/
theorem fiberAvg_eq_of_residueReduction_eq {m n : ℕ} (h : m ≤ n) (c : ResidueGroup n → ℝ)
    {y z : ResidueGroup n} (hyz : residueReduction h y = residueReduction h z) :
    fiberAvg h c y = fiberAvg h c z := by
  simp only [fiberAvg, hyz]

/-- Averaging over fibres preserves the total average: `⟨Avg_{m,n} c⟩_n = ⟨c⟩_n`. -/
theorem residueAvg_fiberAvg {m n : ℕ} (h : m ≤ n) (c : ResidueGroup n → ℝ) :
    residueAvg n (fiberAvg h c) = residueAvg n c := by
  rw [residueAvg, residueAvg]
  congr 1
  have key : ∀ y' : ResidueGroup n,
      ∑ y ∈ univ.filter (fun y => residueReduction h y' = residueReduction h y), c y' =
        (3 : ℝ) ^ (n - m) * c y' := by
    intro y'
    rw [sum_const, nsmul_eq_mul]
    simp only [eq_comm (a := residueReduction h y')]
    rw [card_filter_residueReduction_eq]
    push_cast
    ring
  simp only [fiberAvg, ← mul_sum, sum_filter]
  rw [sum_comm]
  simp only [← sum_filter, key, ← mul_sum, ← mul_assoc, three_zpow_sub_eq_inv h]
  rw [inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]

end CollatzPosDens
