/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.Away.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# Dyadic rationals modulo `3^k`

The ring of dyadic rationals is `ℤ[1/2] = {n / 2^e : n ∈ ℤ, e ∈ ℕ} ⊆ ℚ`, the localization of `ℤ`
away from `2`. Since `3` is odd, `2` is a unit of the residue ring `G_k = ℤ/3^kℤ`, so the reduction
`ℤ → G_k` extends uniquely to a ring homomorphism `x ↦ [x]_k` from `ℤ[1/2]` to `G_k`; explicitly
`[n / 2^e]_k = n · (2⁻¹)^e`. On integers it is reduction modulo `3^k`.

## Main definitions

* `CollatzPosDens.dyadicRationals`: the subring `ℤ[1/2]` of `ℚ`, as a `ℤ`-subalgebra.
* `CollatzPosDens.dyadicRed k`: the ring homomorphism `ℤ[1/2] → G_k`, `x ↦ [x]_k`.

## Main results

* `CollatzPosDens.mem_dyadicRationals`: `x ∈ ℤ[1/2]` iff `x = n / 2^e` for some `n ∈ ℤ`, `e ∈ ℕ`.
* `CollatzPosDens.isUnit_two_residueGroup`: `2` is a unit of `G_k`.
* `CollatzPosDens.two_pow_mul_inv_two_pow`: `2^A (2⁻¹)^A = 1` in `G_k`.
* `CollatzPosDens.dyadicRed_intCast`: `[n]_k = n mod 3^k` for `n ∈ ℤ`.
* `CollatzPosDens.dyadicRed_div_two_pow`: `[n / 2^e]_k = n · (2⁻¹)^e`.
* `CollatzPosDens.ringHom_ext_dyadicRationals`: a ring homomorphism out of `ℤ[1/2]` is unique,
  so in particular every ring homomorphism `ℤ[1/2] → G_k` equals `dyadicRed k`.

## Implementation notes

`ℤ[1/2]` is Mathlib's `Localization.subalgebra.ofField ℚ (Submonoid.powers 2)`, which carries
the instance `IsLocalization.Away 2`; `dyadicRed k` is the universal map
`IsLocalization.Away.lift`. The inverse `2⁻¹` in the explicit formula is the inverse of `ZMod`,
which is the ring inverse because `2` is a unit.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The ring of dyadic rationals `ℤ[1/2] = {n / 2^e : n ∈ ℤ, e ∈ ℕ}`, as a subring of `ℚ`. -/
@[collatz_pos_dens "def_s02_dyadic_reduction"]
noncomputable def dyadicRationals : Subalgebra ℤ ℚ :=
  Localization.subalgebra.ofField ℚ (Submonoid.powers (2 : ℤ))
    (powers_le_nonZeroDivisors_of_noZeroDivisors two_ne_zero)

/-- The dyadic rationals `ℤ[1/2]` are the localization of `ℤ` away from `2`. -/
instance : IsLocalization.Away (2 : ℤ) dyadicRationals :=
  Localization.subalgebra.isLocalization_ofField ℚ _ _

/-- A rational number is dyadic iff it is of the form `n / 2^e` with `n ∈ ℤ`, `e ∈ ℕ`. -/
theorem mem_dyadicRationals {x : ℚ} :
    x ∈ dyadicRationals ↔ ∃ (n : ℤ) (e : ℕ), x = n / 2 ^ e := by
  change (∃ (a s : ℤ) (_ : s ∈ Submonoid.powers (2 : ℤ)), x = (a : ℚ) * (s : ℚ)⁻¹) ↔ _
  constructor
  · rintro ⟨a, _, ⟨e, rfl⟩, rfl⟩
    exact ⟨a, e, by push_cast; rw [div_eq_mul_inv]⟩
  · rintro ⟨n, e, rfl⟩
    exact ⟨n, 2 ^ e, ⟨e, rfl⟩, by push_cast; rw [div_eq_mul_inv]⟩

/-- `n / 2^e` is a dyadic rational. -/
theorem intCast_div_two_pow_mem (n : ℤ) (e : ℕ) : (n / 2 ^ e : ℚ) ∈ dyadicRationals :=
  mem_dyadicRationals.2 ⟨n, e, rfl⟩

/-- `2` is coprime to `3^n`. -/
theorem coprime_two_three_pow (n : ℕ) : Nat.Coprime 2 (3 ^ n) :=
  Nat.Coprime.pow_right n (by decide)

/-- `2` is a unit of the residue ring `G_k = ℤ/3^kℤ`. -/
theorem isUnit_two_residueGroup (k : ℕ) : IsUnit (2 : ResidueGroup k) := by
  simpa using (ZMod.unitOfCoprime 2 (coprime_two_three_pow k)).isUnit

/-- In `G_k`, `2^A (2⁻¹)^A = 1`. -/
theorem two_pow_mul_inv_two_pow (k A : ℕ) : (2 : ResidueGroup k) ^ A * 2⁻¹ ^ A = 1 := by
  obtain ⟨u, hu⟩ := isUnit_two_residueGroup k
  rw [← mul_pow, ← hu, ZMod.mul_inv_of_unit _ u.isUnit, one_pow]

/-- The reduction `x ↦ [x]_k` of dyadic rationals modulo `3^k`: the unique ring homomorphism
`ℤ[1/2] → G_k` extending the reduction `ℤ → G_k`. -/
@[collatz_pos_dens "def_s02_dyadic_reduction"]
noncomputable def dyadicRed (k : ℕ) : dyadicRationals →+* ResidueGroup k :=
  IsLocalization.Away.lift (2 : ℤ) (g := Int.castRingHom (ResidueGroup k))
    (by simpa using isUnit_two_residueGroup k)

/-- Any two ring homomorphisms out of `ℤ[1/2]` agree. -/
theorem ringHom_ext_dyadicRationals {R : Type*} [Semiring R]
    (f g : dyadicRationals →+* R) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ)) (RingHom.ext_int _ _)

/-- Every ring homomorphism `ℤ[1/2] → G_k` is the reduction `dyadicRed k`. -/
theorem eq_dyadicRed {k : ℕ} (f : dyadicRationals →+* ResidueGroup k) : f = dyadicRed k :=
  ringHom_ext_dyadicRationals f _

/-- On integers the reduction is reduction modulo `3^k`: `[n]_k = n mod 3^k`. -/
@[simp]
theorem dyadicRed_intCast (k : ℕ) (n : ℤ) :
    dyadicRed k ⟨(n : ℚ), by simp⟩ = (n : ResidueGroup k) := by
  have : (⟨(n : ℚ), by simp⟩ : dyadicRationals) = n :=
    Subtype.ext (by simp)
  rw [this, map_intCast]

/-- The explicit formula `[n / 2^e]_k = n · (2⁻¹)^e`. -/
theorem dyadicRed_div_two_pow (k : ℕ) (n : ℤ) (e : ℕ) :
    dyadicRed k ⟨n / 2 ^ e, intCast_div_two_pow_mem n e⟩ = (n : ResidueGroup k) * 2⁻¹ ^ e := by
  set x : dyadicRationals := ⟨n / 2 ^ e, intCast_div_two_pow_mem n e⟩
  have hx : x * 2 ^ e = n := Subtype.ext (by
    have h : ((2 : dyadicRationals) : ℚ) = 2 := rfl
    simp [x, h])
  have h2 : (2 : ResidueGroup k) * 2⁻¹ = 1 := by
    obtain ⟨u, hu⟩ := isUnit_two_residueGroup k
    rw [← hu]
    exact ZMod.mul_inv_of_unit _ u.isUnit
  have h := congrArg (dyadicRed k) hx
  rw [map_mul, map_pow, map_ofNat, map_intCast] at h
  rw [← h, mul_assoc, ← mul_pow, h2, one_pow, mul_one]

end CollatzPosDens
