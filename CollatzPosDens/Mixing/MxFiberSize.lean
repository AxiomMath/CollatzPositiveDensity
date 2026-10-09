/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Set.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Reduction

/-!
# Fibers of the reduction maps

For `m ≤ n` and `y ∈ G_n`, the fiber of the reduction `π_{n,m} : G_n → G_m` through `y` is
parametrised by `{0, 1, …, 3^{n-m} - 1}` via `t ↦ y + [3^m t]_n`. Indeed `y'` lies in the fiber
exactly when the least nonnegative representative `d` of `y' - y` is divisible by `3^m`, and the
multiples of `3^m` below `3^n` are exactly `3^m t` with `t < 3^{n-m}`.

## Main results

* `CollatzPosDens.bijOn_add_three_pow_mul_residueReduction_fiber`: the map
  `t ↦ y + [3^m t]_n` is a bijection from `{0, …, 3^{n-m} - 1}` onto the fiber
  `{y' ∈ G_n : π_{n,m} y' = π_{n,m} y}`.

## References

* [Mazur, *Collatz positive density*], §13.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `m ≤ n` and `y ∈ G_n`, the map `t ↦ y + [3^m t]_n` is a bijection from
`{0, 1, …, 3^{n-m} - 1}` onto the fiber `{y' ∈ G_n : π_{n,m} y' = π_{n,m} y}`. -/
@[collatz_pos_dens "lem_mx_fiber_size"]
theorem bijOn_add_three_pow_mul_residueReduction_fiber {m n : ℕ} (h : m ≤ n)
    (y : ResidueGroup n) :
    Set.BijOn (fun t : ℕ => y + ((3 ^ m * t : ℕ) : ResidueGroup n)) (Set.Iio (3 ^ (n - m)))
      {y' | residueReduction h y' = residueReduction h y} := by
  have hpow : 3 ^ n = 3 ^ m * 3 ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' h]
  refine ⟨fun t _ => ?_, fun s hs t ht hst => ?_, fun y' hy' => ?_⟩
  · change residueReduction h (y + _) = _
    rw [map_add, residueReduction_natCast, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  · have hlt : ∀ u : ℕ, u < 3 ^ (n - m) → 3 ^ m * u < 3 ^ n := fun u hu => by
      rw [hpow]; exact Nat.mul_lt_mul_of_pos_left hu (by positivity)
    have := congrArg ZMod.val (add_left_cancel hst)
    rw [ZMod.val_natCast_of_lt (hlt s hs), ZMod.val_natCast_of_lt (hlt t ht)] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  · have h0 : residueReduction h (y' - y) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hy'
    have hdvd : 3 ^ m ∣ (y' - y).val := (residueReduction_eq_zero_iff h _).1 h0
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t, ?_, ?_⟩
    · have := val_lt_three_pow (y' - y)
      rw [ht, hpow] at this
      exact Set.mem_Iio.2 (Nat.lt_of_mul_lt_mul_left this)
    · simp only
      rw [← ht, ZMod.natCast_zmod_val, add_sub_cancel]

end CollatzPosDens
