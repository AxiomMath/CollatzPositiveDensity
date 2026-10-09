/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# Reduction between residue spaces

Write `G_q = ℤ/3^qℤ` for the ternary residue space `CollatzPosDens.ResidueGroup q`, and `ỹ` for
the least nonnegative representative `ZMod.val y` of `y ∈ G_q`. For `m ≤ q` the reduction map
`π_{q,m} : G_q → G_m` sends a residue modulo `3^q` to its residue modulo `3^m`. Since
`3^m ∣ 3^q`, it is a ring homomorphism.

## Main definitions

* `CollatzPosDens.residueReduction h`: for `h : m ≤ q`, the reduction `π_{q,m}` as a ring
  homomorphism `ResidueGroup q →+* ResidueGroup m`.

## Main results

* `CollatzPosDens.residueReduction_natCast`, `CollatzPosDens.residueReduction_intCast`:
  `π_{q,m}` sends the class of `n : ℕ` or `n : ℤ` to the class of `n`.
* `CollatzPosDens.val_residueReduction`: the least nonnegative representative of `π_{q,m} y`
  is `ỹ mod 3^m`.
* `CollatzPosDens.residueReduction_eq_zero_iff`: `π_{q,m} y = 0` iff `3^m ∣ ỹ`.
* `CollatzPosDens.residueReduction_self`: `π_{q,q}` is the identity.
* `CollatzPosDens.residueReduction_residueReduction`: `π_{m,k} (π_{q,m} y) = π_{q,k} y`.
* `CollatzPosDens.residueReduction_comp`: `π_{m,k} ∘ π_{q,m} = π_{q,k}`.
* `CollatzPosDens.card_filter_residueReduction_eq`: every fibre of `π_{q,m}` has `3^{q-m}`
  elements.

## Implementation notes

The map is Mathlib's `ZMod.castHom` applied to the divisibility `3^m ∣ 3^q`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `m ≤ q`, the reduction `π_{q,m} : G_q → G_m` modulo `3^m`, as a ring homomorphism. -/
@[collatz_pos_dens "def_s02_reduction"]
def residueReduction {m q : ℕ} (h : m ≤ q) : ResidueGroup q →+* ResidueGroup m :=
  ZMod.castHom (pow_dvd_pow 3 h) _

/-- The reduction `π_{q,m}` is Mathlib's cast `ZMod (3 ^ q) → ZMod (3 ^ m)`. -/
theorem residueReduction_apply {m q : ℕ} (h : m ≤ q) (y : ResidueGroup q) :
    residueReduction h y = (y.cast : ResidueGroup m) :=
  rfl

/-- Reduction sends the class of a natural number to the class of the same number. -/
theorem residueReduction_natCast {m q : ℕ} (h : m ≤ q) (n : ℕ) :
    residueReduction h (n : ResidueGroup q) = (n : ResidueGroup m) :=
  map_natCast _ n

/-- Reduction sends the class of an integer to the class of the same integer. -/
theorem residueReduction_intCast {m q : ℕ} (h : m ≤ q) (n : ℤ) :
    residueReduction h (n : ResidueGroup q) = (n : ResidueGroup m) :=
  map_intCast _ n

/-- The least nonnegative representative of `π_{q,m} y` is `ỹ mod 3^m`. -/
theorem val_residueReduction {m q : ℕ} (h : m ≤ q) (y : ResidueGroup q) :
    (residueReduction h y).val = y.val % 3 ^ m := by
  conv_lhs => rw [← ZMod.natCast_zmod_val y]
  rw [residueReduction_natCast, ZMod.val_natCast]

/-- The kernel of `π_{q,m}`: `π_{q,m} y = 0` iff `3^m ∣ ỹ`. -/
theorem residueReduction_eq_zero_iff {m q : ℕ} (h : m ≤ q) (y : ResidueGroup q) :
    residueReduction h y = 0 ↔ 3 ^ m ∣ y.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val y]
  rw [residueReduction_natCast, ZMod.natCast_eq_zero_iff]

/-- The reduction `π_{q,q}` is the identity. -/
@[simp]
theorem residueReduction_self (q : ℕ) (y : ResidueGroup q) :
    residueReduction (le_refl q) y = y := by
  simp [residueReduction]

/-- Reductions compose: `π_{m,k} ∘ π_{q,m} = π_{q,k}` as ring homomorphisms. -/
@[simp]
theorem residueReduction_comp {k m q : ℕ} (hkm : k ≤ m) (hmq : m ≤ q) :
    (residueReduction hkm).comp (residueReduction hmq) = residueReduction (hkm.trans hmq) :=
  ZMod.castHom_comp _ _

/-- Reductions compose: `π_{m,k} (π_{q,m} y) = π_{q,k} y`. -/
@[simp]
theorem residueReduction_residueReduction {k m q : ℕ} (hkm : k ≤ m) (hmq : m ≤ q)
    (y : ResidueGroup q) :
    residueReduction hkm (residueReduction hmq y) = residueReduction (hkm.trans hmq) y :=
  RingHom.congr_fun (residueReduction_comp hkm hmq) y

open Finset in
/-- Every fibre of the reduction `π_{q,m}` has exactly `3^{q-m}` elements. -/
theorem card_filter_residueReduction_eq {m q : ℕ} (h : m ≤ q) (b : ResidueGroup m) :
    #{x : ResidueGroup q | residueReduction h x = b} = 3 ^ (q - m) := by
  have hsurj : Function.Surjective (residueReduction h) := ZMod.ringHom_surjective _
  have hfib : ∀ b' : ResidueGroup m, #{x : ResidueGroup q | residueReduction h x = b'} =
      #{x : ResidueGroup q | residueReduction h x = b} := fun b' =>
    AddMonoidHom.card_fiber_eq_of_mem_range (residueReduction h).toAddMonoidHom
      (hsurj b') (hsurj b)
  have htot := card_eq_sum_card_fiberwise (f := residueReduction h)
    (s := (univ : Finset (ResidueGroup q))) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))
  simp only [hfib, sum_const, card_univ, ZMod.card, smul_eq_mul] at htot
  have hpow : 3 ^ q = 3 ^ m * 3 ^ (q - m) := by rw [← pow_add, Nat.add_sub_cancel' h]
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) m) (htot.symm.trans hpow)

end CollatzPosDens
