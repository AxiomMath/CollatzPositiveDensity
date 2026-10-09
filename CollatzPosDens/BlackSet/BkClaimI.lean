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

/-!
# Doubling of the angle at the south neighbour of a point

Let `p = (j, l) ∈ 𝒫` and let `A₀, B₀ ∈ ℝ` with `2 A₀ + B₀ < 1`, `|ϑ(j, l)| ≤ A₀` and
`|ϑ(j, l - 1)| ≤ B₀`. Then `2 ϑ(j, l) = ϑ(j, l - 1)`.

Writing `v = 3^n ϑ(j, l)` and `v₂ = 3^n ϑ(j, l - 1)`, these integers represent `r(j, l)` and
`r(j, l - 1) = 2 r(j, l)`. Hence `3^n ∣ 2 v - v₂`, while `|2 v - v₂| ≤ (2 A₀ + B₀) 3^n < 3^n`,
so `v₂ = 2 v`; dividing by `3^n` gives the claim.

## Main results

* `CollatzPosDens.two_mul_bkTheta_eq_of_self_of_south`: if `|ϑ(j, l)| ≤ A₀`,
  `|ϑ(j, l - 1)| ≤ B₀` and `2 A₀ + B₀ < 1`, then `2 ϑ(j, l) = ϑ(j, l - 1)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `p = (j, l) ∈ 𝒫`, `2 A₀ + B₀ < 1`, `|ϑ(j, l)| ≤ A₀` and `|ϑ(j, l - 1)| ≤ B₀`, then
`2 ϑ(j, l) = ϑ(j, l - 1)`. -/
@[collatz_pos_dens "lem_bk_claim_i"]
theorem two_mul_bkTheta_eq_of_self_of_south (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ}
    (hp : (j, l) ∈ bkPoints) {A₀ B₀ : ℝ} (hAB : 2 * A₀ + B₀ < 1)
    (hA : |bkTheta n ξ (j, l)| ≤ A₀) (hB : |bkTheta n ξ (j, l - 1)| ≤ B₀) :
    2 * bkTheta n ξ (j, l) = bkTheta n ξ (j, l - 1) := by
  rw [mem_bkPoints_mk] at hp
  have hq : (j, l - 1) ∈ bkPoints := mem_bkPoints_mk.2 hp
  have hr := bkThetaResidue_shift n ξ (a := (j, l)) (mem_bkPoints_mk.2 hp) hq
    (by dsimp [bkJ, bkL]; omega) (by dsimp [bkJ, bkL]; omega)
  simp only [bkJ, bkL, sub_self, sub_sub_cancel, Int.toNat_one, Int.toNat_zero, pow_one,
    pow_zero, one_mul] at hr
  have hN : (0 : ℝ) < ((3 ^ n : ℕ) : ℝ) := by positivity
  set v : ℤ := (bkThetaResidue n ξ (j, l)).valMinAbs with hv
  set v₂ : ℤ := (bkThetaResidue n ξ (j, l - 1)).valMinAbs with hv₂
  have hθ : bkTheta n ξ (j, l) = (v : ℝ) / ((3 ^ n : ℕ) : ℝ) := by
    rw [bkTheta_def, sfr_def]
  have hθ₂ : bkTheta n ξ (j, l - 1) = (v₂ : ℝ) / ((3 ^ n : ℕ) : ℝ) := by
    rw [bkTheta_def, sfr_def]
  rw [hθ, abs_div, abs_of_pos hN, div_le_iff₀ hN] at hA
  rw [hθ₂, abs_div, abs_of_pos hN, div_le_iff₀ hN] at hB
  have hdvd : ((3 ^ n : ℕ) : ℤ) ∣ 2 * v - v₂ := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hv, hv₂, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, hr]
    push_cast
    ring
  have hsmall : |2 * v - v₂| < ((3 ^ n : ℕ) : ℤ) := by
    have : |((2 * v - v₂ : ℤ) : ℝ)| < ((3 ^ n : ℕ) : ℝ) := by
      push_cast at hA hB ⊢
      calc |2 * (v : ℝ) - v₂| ≤ |2 * (v : ℝ)| + |(v₂ : ℝ)| := abs_sub _ _
        _ = 2 * |(v : ℝ)| + |(v₂ : ℝ)| := by rw [abs_mul, abs_two]
        _ ≤ (2 * A₀ + B₀) * 3 ^ n := by linarith
        _ < 3 ^ n := by nlinarith [pow_pos (three_pos (α := ℝ)) n]
    exact_mod_cast this
  rw [hθ, hθ₂, ← mul_div_assoc]
  congr 1
  exact_mod_cast sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd hdvd hsmall)

end CollatzPosDens
