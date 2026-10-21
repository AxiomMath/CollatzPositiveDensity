/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkResidueShift

/-!
# Angles above the column top, to height seventeen

Let `t ∈ 𝒫`, write `Q = 3^n`, and let `M₀` be an integer such that `2^h` divides the integer
`Q M₀ + Q ϑ(t)`. Then for every `s ≥ 0` the angle at `t + (s, h)` agrees, up to an integer,
with `9^s (M₀ + ϑ(t)) / 2^h`. Indeed `N = Q ϑ(t)` represents the angle residue `r(t)`, the
residue shift gives `2^h r(t + (s, h)) = 9^s r(t)`, and since `2` is invertible modulo the odd
number `Q` the integer `K = 9^s (Q M₀ + N) / 2^h` represents `r(t + (s, h))`; two
representatives of the same residue differ by a multiple of `Q`.

Applied at the corner `(j(e), l_Δ)` of the canonical triangle `Δ = Δ(e)` of a black point `e`,
with `2^{17}` dividing `Q M₀ + Q ϑ(j(e), l_Δ)`, this gives the statement for all heights
`0 ≤ h ≤ 17` above the column top.

## Main results

* `CollatzPosDens.exists_bkTheta_sub_eq_intCast`: for `t ∈ 𝒫` and `2^h ∣ Q M₀ + Q ϑ(t)`,
  `ϑ(j(t) + s, l(t) + h) - 9^s (M₀ + ϑ(t)) / 2^h ∈ ℤ`.
* `CollatzPosDens.BkBlack.exists_c3H17Angle_sub_eq_intCast`: the same at the corner of `Δ(e)`
  for a black point `e`, under `2^{17} ∣ Q M₀ + Q ϑ(j(e), l_Δ)` and `0 ≤ h ≤ 17`.

## Implementation notes

Divisibility of the real number `3^n M₀ + 3^n ϑ(t)` by `2^h` is stated as the existence of an
integer `k` with `3^n M₀ + 3^n ϑ(t) = 2^h k`; this is divisibility in `ℤ`, since `3^n ϑ(t)` is
an integer. The general statement `exists_bkTheta_sub_eq_intCast` needs neither blackness nor
the canonical triangle, only `t ∈ 𝒫`, and replaces the exponent `17` by the height `h` itself.
In `BkBlack.exists_c3H17Angle_sub_eq_intCast` the hypothesis `e ∈ 𝒫` is the one under which
the canonical triangle `Δ(e)` is formed; blackness of `e` is assumed but is not used by the
argument.

## References

* [Mazur, *Collatz positive density*], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `t ∈ 𝒫`, an integer `M₀` and `s, h ≥ 0` such that `2^h` divides
`3^n M₀ + 3^n ϑ(t)`, the difference `ϑ(j(t) + s, l(t) + h) - 9^s (M₀ + ϑ(t)) / 2^h` is an
integer. -/
theorem exists_bkTheta_sub_eq_intCast {n : ℕ} (ξ : ResidueGroup n) {t : ℤ × ℤ}
    (ht : t ∈ bkPoints) (M₀ : ℤ) (s h : ℕ)
    (hdvd : ∃ k : ℤ, (3 : ℝ) ^ n * M₀ + 3 ^ n * bkTheta n ξ t = 2 ^ h * k) :
    ∃ z : ℤ, bkTheta n ξ (bkJ t + s, bkL t + h) -
      9 ^ s * (M₀ + bkTheta n ξ t) / 2 ^ h = z := by
  obtain ⟨k, hk⟩ := hdvd
  set N := (bkThetaResidue n ξ t).valMinAbs with hN
  set V := (bkThetaResidue n ξ (bkJ t + s, bkL t + h)).valMinAbs with hV
  have hQ : (3 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hθt : bkTheta n ξ t = N / 3 ^ n := by
    rw [bkTheta_def, sfr_def]; push_cast; rfl
  have hθy : bkTheta n ξ (bkJ t + s, bkL t + h) = V / 3 ^ n := by
    rw [bkTheta_def, sfr_def]; push_cast; rfl
  have hkZ : (3 : ℤ) ^ n * M₀ + N = 2 ^ h * k := by
    rw [hθt, mul_div_cancel₀ _ hQ] at hk
    exact_mod_cast hk
  have ht' : (bkJ t + s, bkL t) ∈ bkPoints := by
    rw [mem_bkPoints_mk]; have := mem_bkPoints.1 ht; omega
  have hy : (bkJ t + s, bkL t + h) ∈ bkPoints := by
    rw [mem_bkPoints_mk]; have := mem_bkPoints.1 ht; omega
  have h1 := bkThetaResidue_shift n ξ ht ht' (by dsimp [bkJ]; omega) (by dsimp [bkL]; omega)
  have h2 := bkThetaResidue_shift n ξ hy ht' (by dsimp [bkJ]; omega) (by dsimp [bkL]; omega)
  simp only [bkJ, bkL, add_sub_cancel_left, sub_self, Int.toNat_natCast, Int.toNat_zero,
    pow_zero, mul_one, one_mul, Int.toNat_natCast] at h1 h2
  push_cast at h1 h2
  have hrt : bkThetaResidue n ξ t = (N : ResidueGroup n) := (ZMod.coe_valMinAbs _).symm
  have hry : bkThetaResidue n ξ (bkJ t + s, bkL t + h) = ((9 ^ s * k : ℤ) : ResidueGroup n) := by
    apply ((isUnit_two_residueGroup n).pow h).mul_left_cancel
    have h3 : ((3 ^ n : ℕ) : ResidueGroup n) = 0 := ZMod.natCast_self _
    have hNZ : (N : ResidueGroup n) = ((2 ^ h * k - 3 ^ n * M₀ : ℤ) : ResidueGroup n) := by
      rw [← hkZ]; ring_nf
    rw [← hrt] at hNZ
    have h3' : (3 : ResidueGroup n) ^ n = 0 := by exact_mod_cast h3
    change (2 : ResidueGroup n) ^ h * bkThetaResidue n ξ (t.1 + s, t.2 + h) = _
    rw [← h2, h1, hNZ]
    push_cast
    rw [h3']
    ring
  obtain ⟨z, hz⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1
    ((ZMod.coe_valMinAbs (bkThetaResidue n ξ (bkJ t + s, bkL t + h))).trans hry)
  rw [← hV] at hz
  have hzR : (9 : ℝ) ^ s * k - V = 3 ^ n * z := by exact_mod_cast hz
  have hkR : (3 : ℝ) ^ n * M₀ + N = 2 ^ h * k := by exact_mod_cast hkZ
  refine ⟨-z, ?_⟩
  rw [hθy, hθt]
  field_simp
  push_cast
  linear_combination (-(2 : ℝ) ^ h) * hzR - 9 ^ s * hkR

/-- **Angles above the column top, to height seventeen.** Let `e ∈ 𝒫` be black, `Δ = Δ(e)` its
canonical triangle, and `M₀` an integer such that `2^{17}` divides
`3^n M₀ + 3^n ϑ(j(e), l_Δ)`. Then for all `s ≥ 0` and `0 ≤ h ≤ 17`,
`ϑ(j(e) + s, l_Δ + h) - 9^s (M₀ + ϑ(j(e), l_Δ)) / 2^h` is an integer. -/
@[collatz_pos_dens "lem_c3_h17_angle"]
theorem BkBlack.exists_c3H17Angle_sub_eq_intCast {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {e : ℤ × ℤ} (_he : BkBlack n ξ ε e) (hp : e ∈ bkPoints) (M₀ : ℤ)
    (hdvd : ∃ k : ℤ, (3 : ℝ) ^ n * M₀ +
      3 ^ n * bkTheta n ξ (bkJ e, (bkCanonTriangle n ξ ε e hp).l) = 2 ^ 17 * k)
    (s h : ℕ) (hh : h ≤ 17) :
    ∃ z : ℤ, bkTheta n ξ (bkJ e + s, (bkCanonTriangle n ξ ε e hp).l + h) -
      9 ^ s * (M₀ + bkTheta n ξ (bkJ e, (bkCanonTriangle n ξ ε e hp).l)) / 2 ^ h = z := by
  obtain ⟨k, hk⟩ := hdvd
  refine exists_bkTheta_sub_eq_intCast (t := (bkJ e, (bkCanonTriangle n ξ ε e hp).l)) ξ
    (mem_bkPoints_mk.2 (mem_bkPoints.1 hp)) M₀ s h ⟨2 ^ (17 - h) * k, ?_⟩
  rw [hk]
  push_cast
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hh]

end CollatzPosDens
