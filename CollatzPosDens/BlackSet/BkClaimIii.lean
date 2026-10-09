/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSignedFrac
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkResidueShift
public import CollatzPosDens.BlackSet.BkSfrRep

/-!
# The angle at a point from its west and south neighbours

Let `p = (j, l) ∈ 𝒫` with `j ≥ 2`, and let `A₀, B₀ ∈ ℝ` with `18 A₀ + B₀ < 1`,
`|ϑ(j - 1, l)| ≤ A₀` and `|ϑ(j, l - 1)| ≤ B₀`. Then `2 ϑ(j, l) = ϑ(j, l - 1)`.

Write `v₁ = 3ⁿ ϑ(j - 1, l)` and `v₂ = 3ⁿ ϑ(j, l - 1)`, integer representatives of the angle
residues `r(j - 1, l)` and `r(j, l - 1)`. The residue shift gives `r(p) = 9 r(j - 1, l)` and
`r(j, l - 1) = 2 r(p)`, so `3ⁿ ∣ 18 v₁ - v₂`; since `|18 v₁ - v₂| ≤ (18 A₀ + B₀) 3ⁿ < 3ⁿ`, we get
`v₂ = 18 v₁`. Then `m = 9 v₁` represents `r(p)` with `|m| = |v₂| / 2 < 3ⁿ / 2`, so
`ϑ(p) = m / 3ⁿ` and `2 ϑ(p) = ϑ(j, l - 1)`.

## Main results

* `CollatzPosDens.two_mul_bkTheta_eq_of_west_of_south`: if `18 A₀ + B₀ < 1`,
  `|ϑ(j - 1, l)| ≤ A₀` and `|ϑ(j, l - 1)| ≤ B₀`, then `2 ϑ(j, l) = ϑ(j, l - 1)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `p = (j, l) ∈ 𝒫` with `j ≥ 2`, and `A₀, B₀ ∈ ℝ` with `18 A₀ + B₀ < 1`,
`|ϑ(j - 1, l)| ≤ A₀` and `|ϑ(j, l - 1)| ≤ B₀`. Then `2 ϑ(j, l) = ϑ(j, l - 1)`. -/
@[collatz_pos_dens "lem_bk_claim_iii"]
theorem two_mul_bkTheta_eq_of_west_of_south (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ}
    (hj : 2 ≤ j) {A₀ B₀ : ℝ} (hAB : 18 * A₀ + B₀ < 1)
    (hA : |bkTheta n ξ (j - 1, l)| ≤ A₀) (hB : |bkTheta n ξ (j, l - 1)| ≤ B₀) :
    2 * bkTheta n ξ (j, l) = bkTheta n ξ (j, l - 1) := by
  have hp : (j, l) ∈ bkPoints := mem_bkPoints_mk.2 (by omega)
  have hw : (j - 1, l) ∈ bkPoints := mem_bkPoints_mk.2 (by omega)
  have hs : (j, l - 1) ∈ bkPoints := mem_bkPoints_mk.2 (by omega)
  have h9 : bkThetaResidue n ξ (j, l) = 9 * bkThetaResidue n ξ (j - 1, l) := by
    rw [bkThetaResidue_shift n ξ hw hp (by change j - 1 ≤ j; omega) le_rfl,
      show (bkJ (j, l) - bkJ (j - 1, l)).toNat = 1 by change (j - (j - 1)).toNat = 1; omega,
      show (bkL (j - 1, l) - bkL (j, l)).toNat = 0 by simp]
    norm_num
  have h2 : bkThetaResidue n ξ (j, l - 1) = 2 * bkThetaResidue n ξ (j, l) := by
    rw [bkThetaResidue_shift n ξ hp hs le_rfl (by change l - 1 ≤ l; omega),
      show (bkJ (j, l - 1) - bkJ (j, l)).toNat = 0 by simp,
      show (bkL (j, l) - bkL (j, l - 1)).toNat = 1 by change (l - (l - 1)).toNat = 1; omega]
    norm_num
  set r₁ := bkThetaResidue n ξ (j - 1, l)
  set r₂ := bkThetaResidue n ξ (j, l - 1)
  set v₁ := r₁.valMinAbs
  set v₂ := r₂.valMinAbs
  have hN : (0 : ℝ) < ((3 ^ n : ℕ) : ℝ) := by positivity
  set N : ℝ := ((3 ^ n : ℕ) : ℝ) with hNdef
  have hθ₁ : bkTheta n ξ (j - 1, l) = (v₁ : ℝ) / N := rfl
  have hθ₂ : bkTheta n ξ (j, l - 1) = (v₂ : ℝ) / N := rfl
  rw [hθ₁, abs_div, abs_of_pos hN, div_le_iff₀ hN] at hA
  rw [hθ₂, abs_div, abs_of_pos hN, div_le_iff₀ hN] at hB
  have hA0 : 0 ≤ A₀ := by
    by_contra h
    nlinarith [abs_nonneg (v₁ : ℝ)]
  have hcast : ((18 * v₁ - v₂ : ℤ) : ZMod (3 ^ n)) = 0 := by
    push_cast
    rw [ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, h2, h9]
    ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
  have hlt : |18 * v₁ - v₂| < ((3 ^ n : ℕ) : ℤ) := by
    have : |((18 * v₁ - v₂ : ℤ) : ℝ)| < N := by
      push_cast
      calc |18 * (v₁ : ℝ) - v₂| ≤ 18 * |(v₁ : ℝ)| + |(v₂ : ℝ)| := by
            have := abs_sub (18 * (v₁ : ℝ)) v₂
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 18)] at this
            exact this
        _ ≤ (18 * A₀ + B₀) * N := by nlinarith
        _ < 1 * N := by gcongr
        _ = N := one_mul N
    rw [hNdef] at this
    exact_mod_cast this
  have hv : v₂ = 18 * v₁ := by
    have := Int.eq_zero_of_abs_lt_dvd hcast hlt
    omega
  have hm : ((9 * v₁ : ℤ) : ZMod (3 ^ n)) = bkThetaResidue n ξ (j, l) := by
    push_cast
    rw [ZMod.coe_valMinAbs, h9]
  have hB1 : B₀ < 1 := by linarith
  have hsmall : |((9 * v₁ : ℤ) : ℝ)| < N / 2 := by
    have h' : ((v₂ : ℤ) : ℝ) = 2 * ((9 * v₁ : ℤ) : ℝ) := by rw [hv]; push_cast; ring
    rw [h', abs_mul, abs_two] at hB
    nlinarith
  have hθ : bkTheta n ξ (j, l) = ((9 * v₁ : ℤ) : ℝ) / N := sfr_eq_of_abs_lt hm hsmall
  rw [hθ, hθ₂, hv]
  push_cast
  ring

end CollatzPosDens
