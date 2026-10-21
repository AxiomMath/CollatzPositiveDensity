/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChColtopAngle
public import CollatzPosDens.CharSum.ChColtopOdd

/-!
# Odd dyadic exits

Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black with canonical triangle
`Δ(p) = (j_Δ, l_Δ, s_Δ)`, and `ω ∈ ℕ` with `l(p) + ω = l_Δ`. For integers `r` and `o ≥ 1` put
`e = (j(p) + r, l_Δ + o)`. Then `ϑ(e) = (b + β) / 2^o` for an odd integer `b` and a real `β`
with `|β| ≤ 9^r ε 2^{-ω}`.

Write `h = (j(p), l_Δ)` and `q = (j(p) + r, l_Δ)`, and let `N = 3^n ϑ(h)` and `A = 3^n ϑ(e)`
be the signed representatives of the angle residues `r(h)` and `r(e)`. The residue shift gives
`r(q) = 9^r r(h)` and `r(q) = 2^o r(e)`, so `2^o A = 9^r N + b 3^n` for an integer `b`. As
`2^o A` is even while `9^r N` and `3^n` are odd, `b` is odd; dividing by `2^o 3^n` gives
`ϑ(e) = (b + 9^r ϑ(h)) / 2^o`, and `|9^r ϑ(h)| ≤ 9^r ε 2^{-ω}` by the angle bound on the top
row of `Δ(p)`.

## Main results

* `CollatzPosDens.exists_odd_bkTheta_dyadic_exit`: `ϑ(e) = (b + β) / 2^o` with `b` odd and
  `|β| ≤ 9^r ε 2^{-ω}`.

## Implementation notes

The source assumes `1 ≤ r ≤ f_ω`, where `f_ω` is the exit width. The identity holds for every
`r ∈ ℕ`, so these bounds are dropped.

## References

* [Mazur, *Collatz positive density*], §7.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Odd dyadic exits.** Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black with canonical
triangle `Δ(p) = (j_Δ, l_Δ, s_Δ)`, `ω ∈ ℕ` with `l(p) + ω = l_Δ`, `r ∈ ℕ` and `o ≥ 1`. Then for
`e = (j(p) + r, l_Δ + o)` there are an odd integer `b` and a real `β` with
`|β| ≤ 9^r ε 2^{-ω}` and `ϑ(e) = (b + β) / 2^o`. -/
@[collatz_pos_dens "lem_ch_odd_dyadic_exit"]
theorem exists_odd_bkTheta_dyadic_exit {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (ω : ℕ)
    (hω : bkL p + ω = (bkCanonTriangle n ξ ε p hp).l) (r o : ℕ) (ho : 1 ≤ o) :
    ∃ b : ℤ, Odd b ∧ ∃ β : ℝ, |β| ≤ 9 ^ r * ε * (2 : ℝ) ^ (-(ω : ℤ)) ∧
      bkTheta n ξ (bkJ p + r, (bkCanonTriangle n ξ ε p hp).l + o) = (b + β) / 2 ^ o := by
  set L := (bkCanonTriangle n ξ ε p hp).l
  set h : ℤ × ℤ := (bkJ p, L)
  set q : ℤ × ℤ := (bkJ p + r, L)
  set e : ℤ × ℤ := (bkJ p + r, L + o)
  have hp1 : 1 ≤ bkJ p := hp
  have hh : h ∈ bkPoints := mem_bkPoints_mk.2 hp1
  have hq : q ∈ bkPoints := mem_bkPoints_mk.2 (by omega)
  have he : e ∈ bkPoints := mem_bkPoints_mk.2 (by omega)
  -- The two residue shifts.
  have hsh := bkThetaResidue_shift n ξ hh hq (by change bkJ p ≤ bkJ p + r; omega) le_rfl
  have hse := bkThetaResidue_shift n ξ he hq le_rfl (by change L ≤ L + o; omega)
  have h1 : (bkJ q - bkJ h).toNat = r := by change (bkJ p + r - bkJ p).toNat = r; simp
  have h2 : (bkL h - bkL q).toNat = 0 := by change (L - L).toNat = 0; simp
  have h3 : (bkJ q - bkJ e).toNat = 0 := by change (bkJ p + r - (bkJ p + r)).toNat = 0; simp
  have h4 : (bkL e - bkL q).toNat = o := by change (L + o - L).toNat = o; simp
  rw [h1, h2] at hsh
  rw [h3, h4] at hse
  set N := (bkThetaResidue n ξ h).valMinAbs
  set A := (bkThetaResidue n ξ e).valMinAbs
  -- `2^o A ≡ 9^r N (mod 3^n)`.
  have hcong : (((2 ^ o * A - 9 ^ r * N : ℤ)) : ResidueGroup n) = 0 := by
    push_cast
    rw [ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
    have := hsh.symm.trans hse
    push_cast at this
    linear_combination -this
  obtain ⟨b, hbN⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcong
  push_cast at hbN
  -- `b` is odd.
  have hNodd : Odd N := odd_valMinAbs_bkThetaResidue_bkColTop hξ hε₀ hε hp hb
  have hbodd : Odd b := by
    have hev : Even (2 ^ o * A) :=
      ((Int.even_pow.2 ⟨even_two, by omega⟩ : Even ((2 : ℤ) ^ o))).mul_right A
    have h9N : Odd (9 ^ r * N) := (Odd.pow (by decide)).mul hNodd
    have h3n : Odd ((3 : ℤ) ^ n) := Odd.pow (by decide)
    have heq : 2 ^ o * A = 9 ^ r * N + 3 ^ n * b := by linarith
    by_contra hbe
    rw [Int.not_odd_iff_even] at hbe
    have : Odd (2 ^ o * A) := heq ▸ h9N.add_even (hbe.mul_left _)
    exact (Int.not_even_iff_odd.2 this) hev
  refine ⟨b, hbodd, 9 ^ r * bkTheta n ξ h, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 9 ^ r), mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_bkTheta_colTop_le hξ hε₀ hε hp hb ω hω)
      (by positivity)
  · have hθe := three_pow_mul_bkTheta n ξ e
    have hθh := three_pow_mul_bkTheta n ξ h
    have hbR : ((2 : ℝ) ^ o * A - 9 ^ r * N) = 3 ^ n * b := by exact_mod_cast hbN
    have h3 : (0 : ℝ) < 3 ^ n := by positivity
    have h2 : (0 : ℝ) < 2 ^ o := by positivity
    rw [eq_div_iff h2.ne']
    apply mul_left_cancel₀ h3.ne'
    calc (3 : ℝ) ^ n * (bkTheta n ξ e * 2 ^ o) = 2 ^ o * ((3 : ℝ) ^ n * bkTheta n ξ e) := by ring
      _ = 2 ^ o * A := by rw [hθe]
      _ = 3 ^ n * b + 9 ^ r * N := by linarith
      _ = 3 ^ n * b + 9 ^ r * ((3 : ℝ) ^ n * bkTheta n ξ h) := by rw [hθh]
      _ = 3 ^ n * (b + 9 ^ r * bkTheta n ξ h) := by ring

end CollatzPosDens
