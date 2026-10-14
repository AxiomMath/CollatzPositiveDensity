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

/-- One step west multiplies the angle residue by `9`. -/
theorem bkThetaResidue_west (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ} (hj : 2 ≤ j) :
    bkThetaResidue n ξ (j, l) = 9 * bkThetaResidue n ξ (j - 1, l) := by
  rw [bkThetaResidue_shift n ξ (a := (j - 1, l)) (q := (j, l)) (mem_bkPoints_mk.2 (by omega))
    (mem_bkPoints_mk.2 (by omega)) (by simp [bkJ]) le_rfl]
  simp [bkJ]

/-- One step south multiplies the angle residue by `2`. -/
theorem bkThetaResidue_south (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ} (hj : 1 ≤ j) :
    bkThetaResidue n ξ (j, l - 1) = 2 * bkThetaResidue n ξ (j, l) := by
  rw [bkThetaResidue_shift n ξ (a := (j, l)) (q := (j, l - 1)) (mem_bkPoints_mk.2 hj)
    (mem_bkPoints_mk.2 hj) le_rfl (by simp [bkL])]
  simp [bkL]

/-- Let `p = (j, l) ∈ 𝒫` with `j ≥ 2`, and `A₀, B₀ ∈ ℝ` with `18 A₀ + B₀ < 1`,
`|ϑ(j - 1, l)| ≤ A₀` and `|ϑ(j, l - 1)| ≤ B₀`. Then `2 ϑ(j, l) = ϑ(j, l - 1)`. -/
@[collatz_pos_dens "lem_bk_claim_iii"]
theorem two_mul_bkTheta_eq_of_west_of_south (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ}
    (hj : 2 ≤ j) {A₀ B₀ : ℝ} (hAB : 18 * A₀ + B₀ < 1)
    (hA : |bkTheta n ξ (j - 1, l)| ≤ A₀) (hB : |bkTheta n ξ (j, l - 1)| ≤ B₀) :
    2 * bkTheta n ξ (j, l) = bkTheta n ξ (j, l - 1) := by
  have h9 := bkThetaResidue_west n ξ (l := l) hj
  have h2 := bkThetaResidue_south n ξ (l := l) (by omega : 1 ≤ j)
  set v₁ := (bkThetaResidue n ξ (j - 1, l)).valMinAbs
  set v₂ := (bkThetaResidue n ξ (j, l - 1)).valMinAbs
  have hN : (0 : ℝ) < ((3 ^ n : ℕ) : ℝ) := by positivity
  set N : ℝ := ((3 ^ n : ℕ) : ℝ) with hNdef
  have hθ₂ : bkTheta n ξ (j, l - 1) = (v₂ : ℝ) / N := rfl
  rw [show bkTheta n ξ (j - 1, l) = (v₁ : ℝ) / N from rfl, abs_div, abs_of_pos hN,
    div_le_iff₀ hN] at hA
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
            simpa [abs_mul] using abs_sub (18 * (v₁ : ℝ)) v₂
        _ ≤ (18 * A₀ + B₀) * N := by nlinarith
        _ < N := by nlinarith
    rw [hNdef] at this
    exact_mod_cast this
  have hv : v₂ = 18 * v₁ := by
    have := Int.eq_zero_of_abs_lt_dvd hcast hlt
    omega
  have hm : ((9 * v₁ : ℤ) : ZMod (3 ^ n)) = bkThetaResidue n ξ (j, l) := by
    push_cast
    rw [ZMod.coe_valMinAbs, h9]
  have hsmall : |((9 * v₁ : ℤ) : ℝ)| < N / 2 := by
    have h' : ((v₂ : ℤ) : ℝ) = 2 * ((9 * v₁ : ℤ) : ℝ) := by
      rw [hv]
      push_cast
      ring
    rw [h', abs_mul, abs_two] at hB
    nlinarith
  rw [show bkTheta n ξ (j, l) = ((9 * v₁ : ℤ) : ℝ) / N from sfr_eq_of_abs_lt hm hsmall, hθ₂, hv]
  push_cast
  ring

end CollatzPosDens
