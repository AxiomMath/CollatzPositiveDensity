/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.Transfer.DyadicReduction

/-!
# The angle residue

For a point `(j, l) ∈ 𝒫`, a level `n` and a residue `ξ ∈ G_n`, the *angle residue* is
`r_{n,ξ}(j, l) = [3^{2(j-1)} 2^{1-l}]_n · ξ ∈ G_n`, where `3^{2(j-1)} 2^{1-l}` is a dyadic
rational and `[·]_n : ℤ[1/2] → G_n` is the reduction modulo `3^n`.

## Main definitions

* `CollatzPosDens.dyadicTwoUnit`: `2` as a unit of `ℤ[1/2]`.
* `CollatzPosDens.bkThetaDyadic p`: the dyadic rational `3^{2(j-1)} 2^{1-l}` of `p = (j, l)`.
* `CollatzPosDens.bkThetaResidue n ξ p`: the angle residue `r_{n,ξ}(p)`.

## Main results

* `CollatzPosDens.coe_bkThetaDyadic`: for `p ∈ 𝒫`, the rational number underlying
  `bkThetaDyadic p` is `3^{2(j-1)} · 2^{1-l}`.
* `CollatzPosDens.bkThetaResidue_eq`: `r_{n,ξ}(j, l) = 3^{2(j-1)} · u^{1-l} · ξ`, with `u` the
  unit `2` of `G_n`.

## Implementation notes

The exponent `1 - l` may be negative, so `2^{1-l}` is the integer power of the unit `2` of
`ℤ[1/2]`. The exponent `2(j-1)` is a natural number on `𝒫`; the definition is stated for all of
`ℤ × ℤ`, using `Int.toNat` of the exponent, which agrees with `2(j-1)` on `𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The element `2` as a unit of the dyadic rationals `ℤ[1/2]`. -/
noncomputable def dyadicTwoUnit : dyadicRationalsˣ :=
  (IsLocalization.Away.algebraMap_isUnit (2 : ℤ) (S := dyadicRationals)).unit

/-- The rational number underlying the unit `dyadicTwoUnit` is `2`. -/
@[simp]
theorem coe_dyadicTwoUnit : ((dyadicTwoUnit : dyadicRationals) : ℚ) = 2 := rfl

/-- The dyadic rational `3^{2(j-1)} 2^{1-l}` attached to a point `p = (j, l)`. -/
@[collatz_pos_dens "def_bk_theta_residue"]
noncomputable def bkThetaDyadic (p : ℤ × ℤ) : dyadicRationals :=
  3 ^ (2 * (bkJ p - 1)).toNat * ((dyadicTwoUnit ^ (1 - bkL p) : dyadicRationalsˣ) : _)

/-- The angle residue `r_{n,ξ}(p) = [3^{2(j-1)} 2^{1-l}]_n · ξ ∈ G_n` of a point `p = (j, l)`. -/
@[collatz_pos_dens "def_bk_theta_residue"]
noncomputable def bkThetaResidue (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) : ResidueGroup n :=
  dyadicRed n (bkThetaDyadic p) * ξ

/-- The angle residue `r_{n,ξ}(p)` is the reduction of `bkThetaDyadic p` modulo `3^n`, times
`ξ`. -/
theorem bkThetaResidue_def (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) :
    bkThetaResidue n ξ p = dyadicRed n (bkThetaDyadic p) * ξ := rfl

/-- On `𝒫`, `bkThetaDyadic (j, l)` is the rational number `3^{2(j-1)} · 2^{1-l}`. -/
theorem coe_bkThetaDyadic {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    (bkThetaDyadic p : ℚ) = (3 : ℚ) ^ (2 * (bkJ p - 1)) * (2 : ℚ) ^ (1 - bkL p) := by
  have h : (0 : ℤ) ≤ 2 * (bkJ p - 1) := by simp only [mem_bkPoints] at hp; omega
  rw [bkThetaDyadic, Subalgebra.coe_mul, Subalgebra.coe_pow, ← zpow_natCast,
    Int.toNat_of_nonneg h]
  congr 1
  have h2 : (Units.map (dyadicRationals.val : dyadicRationals →* ℚ) dyadicTwoUnit : ℚ) = 2 := rfl
  rw [← h2, ← Units.val_zpow_eq_zpow_val, ← map_zpow]
  rfl

/-- The explicit formula `r_{n,ξ}(j, l) = 3^{2(j-1)} · u^{1-l} · ξ`, where `u` is `2` as a unit
of `G_n`. -/
theorem bkThetaResidue_eq (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) :
    bkThetaResidue n ξ p = 3 ^ (2 * (bkJ p - 1)).toNat *
      (((isUnit_two_residueGroup n).unit ^ (1 - bkL p) : (ResidueGroup n)ˣ) : _) * ξ := by
  have h2 : Units.map (dyadicRed n : dyadicRationals →* ResidueGroup n) dyadicTwoUnit =
      (isUnit_two_residueGroup n).unit := by
    ext
    change dyadicRed n 2 = 2
    exact map_ofNat _ 2
  rw [bkThetaResidue_def, bkThetaDyadic, map_mul, map_pow, map_ofNat, ← h2, ← map_zpow]
  rfl

end CollatzPosDens
