/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSignedFrac
public import CollatzPosDens.BlackSet.BkThetaResidue

/-!
# The angle of a point

For a point `p ∈ 𝒫`, a level `n` and a residue `ξ ∈ G_n = ℤ/3^nℤ`, the *angle* of `p` is
`ϑ_{n,ξ}(p) := sfr(r_{n,ξ}(p))`, the signed fractional part (with modulus `N = 3^n`) of the
angle residue `r_{n,ξ}(p)`. It is a real number in `(-1/2, 1/2]`.

## Main definitions

* `CollatzPosDens.bkTheta n ξ p`: the angle `ϑ_{n,ξ}(p) = sfr (r_{n,ξ}(p))`.

## Main results

* `CollatzPosDens.bkTheta_mem_Ioc`: `ϑ_{n,ξ}(p) ∈ (-1/2, 1/2]`.
* `CollatzPosDens.abs_bkTheta_le`: `|ϑ_{n,ξ}(p)| ≤ 1/2`.

## Implementation notes

The angle is defined for every `p : ℤ × ℤ`, not only for `p ∈ 𝒫`, since the angle residue
`bkThetaResidue` is.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The angle `ϑ_{n,ξ}(p) := sfr (r_{n,ξ}(p))` of a point `p`: the signed fractional part, with
modulus `3^n`, of the angle residue `r_{n,ξ}(p) ∈ G_n`. -/
@[collatz_pos_dens "def_bk_theta"]
noncomputable def bkTheta (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) : ℝ :=
  sfr (bkThetaResidue n ξ p)

/-- Unfolding lemma for `bkTheta`. -/
theorem bkTheta_def (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) :
    bkTheta n ξ p = sfr (bkThetaResidue n ξ p) := rfl

/-- The angle lies in `(-1/2, 1/2]`. -/
theorem bkTheta_mem_Ioc (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) :
    bkTheta n ξ p ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) :=
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero n three_ne_zero⟩
  sfr_mem_Ioc _

/-- The angle has absolute value at most `1/2`. -/
theorem abs_bkTheta_le (n : ℕ) (ξ : ResidueGroup n) (p : ℤ × ℤ) :
    |bkTheta n ξ p| ≤ 1 / 2 := by
  obtain ⟨h₁, h₂⟩ := bkTheta_mem_Ioc n ξ p
  exact abs_le.2 ⟨by linarith, h₂⟩

end CollatzPosDens
