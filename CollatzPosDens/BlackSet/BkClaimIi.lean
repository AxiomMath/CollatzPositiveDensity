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
# The angle of a point from its east and south neighbours

Let `p = (j, l) ∈ 𝒫` and let `A₀, B₀ ∈ ℝ` with `2 A₀ + 9 B₀ < 1`, `|ϑ(j + 1, l)| ≤ A₀` and
`|ϑ(j, l - 1)| ≤ B₀`. Then `2 ϑ(j, l) = ϑ(j, l - 1)`.

Writing `v₁ = 3^n ϑ(j + 1, l)` and `v₂ = 3^n ϑ(j, l - 1)`, these integers represent
`r(j + 1, l) = 9 r(p)` and `r(j, l - 1) = 2 r(p)`. Hence `3^n ∣ 2 v₁ - 9 v₂`, while
`|2 v₁ - 9 v₂| ≤ (2 A₀ + 9 B₀) 3^n < 3^n`, so `2 v₁ = 9 v₂`. The integer `m = v₁ - 4 v₂` then
represents `r(p)`, satisfies `2 m = v₂`, and is small enough (`|m| < 3^n / 2`) to be the
representative defining `ϑ(p)`.

## Main results

* `CollatzPosDens.two_mul_bkTheta_eq_of_east_of_south`: if `2 A₀ + 9 B₀ < 1`,
  `|ϑ(j + 1, l)| ≤ A₀` and `|ϑ(j, l - 1)| ≤ B₀`, then `2 ϑ(j, l) = ϑ(j, l - 1)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `p = (j, l) ∈ 𝒫`, `2 A₀ + 9 B₀ < 1`, `|ϑ(j + 1, l)| ≤ A₀` and `|ϑ(j, l - 1)| ≤ B₀`, then
`2 ϑ(j, l) = ϑ(j, l - 1)`. -/
@[collatz_pos_dens "lem_bk_claim_ii"]
theorem two_mul_bkTheta_eq_of_east_of_south (n : ℕ) (ξ : ResidueGroup n) {j l : ℤ}
    (hp : (j, l) ∈ bkPoints) {A₀ B₀ : ℝ} (hAB : 2 * A₀ + 9 * B₀ < 1)
    (hA : |bkTheta n ξ (j + 1, l)| ≤ A₀) (hB : |bkTheta n ξ (j, l - 1)| ≤ B₀) :
    2 * bkTheta n ξ (j, l) = bkTheta n ξ (j, l - 1) := by
  rw [mem_bkPoints_mk] at hp
  have hq₁ : (j + 1, l) ∈ bkPoints := mem_bkPoints_mk.2 (by omega)
  have hq₂ : (j, l - 1) ∈ bkPoints := mem_bkPoints_mk.2 hp
  have hr₁ := bkThetaResidue_shift n ξ (a := (j, l)) (mem_bkPoints_mk.2 hp) hq₁
    (by dsimp [bkJ, bkL]; omega) (by dsimp [bkJ, bkL]; omega)
  have hr₂ := bkThetaResidue_shift n ξ (a := (j, l)) (mem_bkPoints_mk.2 hp) hq₂
    (by dsimp [bkJ, bkL]; omega) (by dsimp [bkJ, bkL]; omega)
  simp only [bkJ, bkL, add_sub_cancel_left, sub_self, sub_sub_cancel, Int.toNat_one,
    Int.toNat_zero, pow_one, pow_zero, mul_one, one_mul] at hr₁ hr₂
  have hN : (0 : ℝ) < ((3 ^ n : ℕ) : ℝ) := by positivity
  set v₁ : ℤ := (bkThetaResidue n ξ (j + 1, l)).valMinAbs with hv₁
  set v₂ : ℤ := (bkThetaResidue n ξ (j, l - 1)).valMinAbs with hv₂
  have hθ₁ : bkTheta n ξ (j + 1, l) = (v₁ : ℝ) / ((3 ^ n : ℕ) : ℝ) := by
    rw [bkTheta_def, sfr_def]
  have hθ₂ : bkTheta n ξ (j, l - 1) = (v₂ : ℝ) / ((3 ^ n : ℕ) : ℝ) := by
    rw [bkTheta_def, sfr_def]
  have hA0 : 0 ≤ A₀ := (abs_nonneg _).trans hA
  rw [hθ₁, abs_div, abs_of_pos hN, div_le_iff₀ hN] at hA
  rw [hθ₂, abs_div, abs_of_pos hN, div_le_iff₀ hN] at hB
  have hdvd : ((3 ^ n : ℕ) : ℤ) ∣ 2 * v₁ - 9 * v₂ := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hv₁, hv₂, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, hr₁, hr₂]
    push_cast
    ring
  have hsmall : |2 * v₁ - 9 * v₂| < ((3 ^ n : ℕ) : ℤ) := by
    have : |((2 * v₁ - 9 * v₂ : ℤ) : ℝ)| < ((3 ^ n : ℕ) : ℝ) := by
      push_cast at hA hB ⊢
      calc |2 * (v₁ : ℝ) - 9 * v₂| ≤ |2 * (v₁ : ℝ)| + |9 * (v₂ : ℝ)| := abs_sub _ _
        _ = 2 * |(v₁ : ℝ)| + 9 * |(v₂ : ℝ)| := by norm_num [abs_mul]
        _ ≤ (2 * A₀ + 9 * B₀) * 3 ^ n := by nlinarith
        _ < 3 ^ n := by nlinarith [pow_pos (three_pos (α := ℝ)) n]
    exact_mod_cast this
  have h2m : 2 * (v₁ - 4 * v₂) = v₂ := by linarith [Int.eq_zero_of_abs_lt_dvd hdvd hsmall]
  have hrep : ((v₁ - 4 * v₂ : ℤ) : ZMod (3 ^ n)) = bkThetaResidue n ξ (j, l) := by
    push_cast
    rw [hv₁, hv₂, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, hr₁, hr₂]
    push_cast
    ring
  have hm : |((v₁ - 4 * v₂ : ℤ) : ℝ)| < ((3 ^ n : ℕ) : ℝ) / 2 := by
    have h2m' : 2 * ((v₁ - 4 * v₂ : ℤ) : ℝ) = v₂ := by exact_mod_cast h2m
    have hB9 : 9 * B₀ < 1 := by linarith
    have : |2 * ((v₁ - 4 * v₂ : ℤ) : ℝ)| < ((3 ^ n : ℕ) : ℝ) := by
      rw [h2m']
      nlinarith
    rw [abs_mul, abs_two] at this
    linarith
  rw [bkTheta_def, sfr_eq_of_abs_lt hrep hm, hθ₂, ← mul_div_assoc]
  congr 1
  exact_mod_cast h2m

end CollatzPosDens
