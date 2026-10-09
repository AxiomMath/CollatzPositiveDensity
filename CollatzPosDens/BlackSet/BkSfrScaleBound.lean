/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.ValMinAbs
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSignedFrac

/-!
# Scaling bound for the signed fractional part

For `z : ZMod N` and `k : ℕ`, the signed fractional part satisfies
`|sfr (k z)| ≤ k |sfr z|`. The representative `w` of `k z` in `(-N/2, N/2]` has minimal absolute
value among all integers congruent to `k z`, and `k v` is one of them, where `v` is the
representative of `z`.

## Main results

* `CollatzPosDens.abs_sfr_natCast_mul_le`: `|sfr (k * z)| ≤ k * |sfr z|`.

## Implementation notes

The source assumes `N ≥ 1` odd. Neither hypothesis is needed: for `N = 0` both sides vanish
since `sfr` divides by `N`, and the minimality of `ZMod.valMinAbs` holds for every `N`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- Scaling bound for the signed fractional part: `|sfr (k z)| ≤ k |sfr z|`. -/
@[collatz_pos_dens "lem_bk_sfr_scale_bound"]
theorem abs_sfr_natCast_mul_le {N : ℕ} (z : ZMod N) (k : ℕ) :
    |sfr ((k : ZMod N) * z)| ≤ k * |sfr z| := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [sfr_def]
  have : NeZero N := ⟨hN.ne'⟩
  have hmin : ((k : ZMod N) * z).valMinAbs.natAbs ≤ ((k : ℤ) * z.valMinAbs).natAbs :=
    ZMod.natAbs_min_of_le_div_two N _ _ (by push_cast; simp)
      (ZMod.natAbs_valMinAbs_le _)
  have hmin' : |(((k : ZMod N) * z).valMinAbs : ℝ)| ≤ (k : ℝ) * |(z.valMinAbs : ℝ)| := by
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hmin
    have h : (|((k : ZMod N) * z).valMinAbs| : ℤ) ≤ k * |z.valMinAbs| := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast hmin
    exact_mod_cast h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sfr_def, sfr_def, abs_div, abs_div, abs_of_pos hN', ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hmin' hN'.le

end CollatzPosDens
