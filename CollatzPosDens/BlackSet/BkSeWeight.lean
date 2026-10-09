/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints

/-!
# The weight `se`

For lattice points `a, q` of `CollatzPosDens.bkPoints` the weight is the real number
`se(a, q) = (j(q) - j(a)) log 9 + (l(a) - l(q)) log 2`, so that
`exp (se(a, q)) = 9 ^ (j(q) - j(a)) · 2 ^ (l(a) - l(q))`.

## Main definitions

* `CollatzPosDens.bkSe`: the weight `se(a, q)`.

## Main results

* `CollatzPosDens.bkSe_self`, `CollatzPosDens.bkSe_swap`, `CollatzPosDens.bkSe_add_bkSe`: `se`
  vanishes on the diagonal, is antisymmetric, and is additive along chains of points.
* `CollatzPosDens.bkSe_add_add`: `se` is invariant under translating both points.
* `CollatzPosDens.exp_bkSe`: `exp (se(a, q)) = 9 ^ (j(q) - j(a)) · 2 ^ (l(a) - l(q))`.
* `CollatzPosDens.exp_bkSe_eq_natCast`: for `j(a) ≤ j(q)` and `l(q) ≤ l(a)`, `exp (se(a, q))`
  is that natural number.

## Implementation notes

`se` is defined on all of `ℤ × ℤ`, not only on pairs of points of `bkPoints`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The weight `se(a, q) = (j(q) - j(a)) log 9 + (l(a) - l(q)) log 2`. -/
@[collatz_pos_dens "def_bk_se_weight"]
noncomputable def bkSe (a q : ℤ × ℤ) : ℝ :=
  ((bkJ q - bkJ a : ℤ) : ℝ) * Real.log 9 + ((bkL a - bkL q : ℤ) : ℝ) * Real.log 2

/-- `se(a, q)` unfolds to `(j(q) - j(a)) log 9 + (l(a) - l(q)) log 2`. -/
theorem bkSe_def (a q : ℤ × ℤ) :
    bkSe a q =
      ((bkJ q - bkJ a : ℤ) : ℝ) * Real.log 9 + ((bkL a - bkL q : ℤ) : ℝ) * Real.log 2 :=
  rfl

/-- `se((j, l), (j', l')) = (j' - j) log 9 + (l - l') log 2`. -/
@[simp]
theorem bkSe_mk (j l j' l' : ℤ) :
    bkSe (j, l) (j', l') =
      ((j' - j : ℤ) : ℝ) * Real.log 9 + ((l - l' : ℤ) : ℝ) * Real.log 2 :=
  rfl

/-- `se` vanishes on the diagonal: `se(a, a) = 0`. -/
@[simp]
theorem bkSe_self (a : ℤ × ℤ) : bkSe a a = 0 := by
  simp [bkSe]

/-- `se` is antisymmetric. -/
theorem bkSe_swap (a q : ℤ × ℤ) : bkSe q a = -bkSe a q := by
  simp only [bkSe, Int.cast_sub]; ring

/-- `se` is additive along a chain of points. -/
theorem bkSe_add_bkSe (a b c : ℤ × ℤ) : bkSe a b + bkSe b c = bkSe a c := by
  simp only [bkSe, Int.cast_sub]; ring

/-- `se` is invariant under translating both points by the same vector. -/
@[simp]
theorem bkSe_add_add (a q v : ℤ × ℤ) : bkSe (a + v) (q + v) = bkSe a q := by
  simp only [bkSe, bkJ, bkL, Prod.fst_add, Prod.snd_add, Int.cast_sub, Int.cast_add]; ring

/-- The exponential of `se` is `9 ^ (j(q) - j(a)) · 2 ^ (l(a) - l(q))`. -/
theorem exp_bkSe (a q : ℤ × ℤ) :
    Real.exp (bkSe a q) = (9 : ℝ) ^ (bkJ q - bkJ a) * (2 : ℝ) ^ (bkL a - bkL q) := by
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num),
    Real.rpow_def_of_pos (by norm_num), ← Real.exp_add, bkSe]
  ring_nf

/-- For `j(a) ≤ j(q)` and `l(q) ≤ l(a)`, `exp (se(a, q))` is the natural number
`9 ^ (j(q) - j(a)) · 2 ^ (l(a) - l(q))`. -/
theorem exp_bkSe_eq_natCast {a q : ℤ × ℤ} (hj : bkJ a ≤ bkJ q) (hl : bkL q ≤ bkL a) :
    Real.exp (bkSe a q) =
      ((9 ^ (bkJ q - bkJ a).toNat * 2 ^ (bkL a - bkL q).toNat : ℕ) : ℝ) := by
  obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hj)
  obtain ⟨v, hv⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hl)
  rw [exp_bkSe, hu, hv, Int.toNat_natCast, Int.toNat_natCast, zpow_natCast, zpow_natCast]
  push_cast
  rfl

end CollatzPosDens
