/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkSignedFrac
public import CollatzPosDens.BlackSet.BkColtopSpec
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.BlackSet.BkResidueShift
public import CollatzPosDens.BlackSet.BkSfrRep
public import CollatzPosDens.BlackSet.BkSourceMem
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.BlackSet.BkNwClosure
public import CollatzPosDens.BlackSet.BkBlackOn

/-!
# The column top has an odd numerator

Let `ξ` be a unit, `0 < ε < 1/27` and `p` black, with canonical triangle
`Δ(p) = (j_Δ, l_Δ, s)`. Then the integer `3^n ϑ(j(p), l_Δ)` is odd.

Write `h = (j(p), l_Δ)` and `a = (j(p), l_Δ + 1)`. Since `l_Δ = l_*(p)` is the column top,
`a` is white, while `h` lies in `Δ(p)` and is therefore black. The residue shift gives
`r(h) = 2 r(a)`. If the representative `N = 3^n ϑ(h)` of `r(h)` were even, `N / 2` would be a
representative of `r(a)` of absolute value below `3^n / 2`, so `ϑ(a) = ϑ(h) / 2` and
`|ϑ(a)| ≤ ε / 2 < ε`, contradicting whiteness of `a`.

## Main results

* `CollatzPosDens.odd_valMinAbs_bkThetaResidue_bkColTop`: the signed representative of the angle
  residue at `(j(p), l_*(p))` is odd.
* `CollatzPosDens.odd_three_pow_mul_bkTheta_bkColTop`: the integer `3^n ϑ(j(p), l_*(p))` is odd.

## Implementation notes

The integer `3^n ϑ(h)` is the signed representative `ZMod.valMinAbs (r(h))` of the angle residue;
the statement records it as an integer `N` with `N = 3^n ϑ(h)` in `ℝ` and `N` odd. Black points
are points of `𝒫`, recorded by the hypothesis `p ∈ bkPoints`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The integer `3^n ϑ_{n,ξ}(q)` is the signed representative of the angle residue `r_{n,ξ}(q)`. -/
theorem three_pow_mul_bkTheta (n : ℕ) (ξ : ResidueGroup n) (q : ℤ × ℤ) :
    (3 : ℝ) ^ n * bkTheta n ξ q = ((bkThetaResidue n ξ q).valMinAbs : ℝ) := by
  rw [bkTheta_def, sfr_def]
  push_cast
  field_simp

/-- Let `ξ` be a unit, `0 < ε < 1/27` and `p ∈ 𝒫` black. Then the signed representative of the
angle residue at `(j(p), l_*(p))` is odd. -/
theorem odd_valMinAbs_bkThetaResidue_bkColTop {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1 / 27) {p : ℤ × ℤ}
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) :
    Odd (bkThetaResidue n ξ (bkJ p, bkColTop n ξ ε p)).valMinAbs := by
  set L := bkColTop n ξ ε p
  -- `a = (j(p), l_Δ + 1)` is white.
  obtain ⟨-, -, hwhite⟩ := (eq_bkColTop_iff hξ (by linarith) hp hb L).1 rfl
  -- `h = (j(p), l_Δ)` is black.
  have hpΔ := mem_bkCanonTriangle_self hξ hε₀ hε hp hb
  have hj := BkTriangle.j_le_of_mem hpΔ
  have hl := BkTriangle.le_l_of_mem hpΔ
  have hhΔ : (bkJ p, L) ∈ bkCanonTriangle n ξ ε p hp :=
    BkTriangle.mem_of_mem_of_nw hpΔ hj le_rfl hl le_rfl
  have hhb := bkBlack_of_mem_bkCanonTriangle hξ hε₀ hε hp hb hhΔ
  -- The residue shift `r(h) = 2 r(a)`.
  have h2 : bkThetaResidue n ξ (bkJ p, L) = 2 * bkThetaResidue n ξ (bkJ p, L + 1) := by
    rw [bkThetaResidue_shift n ξ (a := (bkJ p, L + 1)) (q := (bkJ p, L)) (mem_bkPoints.2 hp)
      (mem_bkPoints.2 hp) le_rfl (by change L ≤ L + 1; omega)]
    have h1 : (bkL (bkJ p, L + 1) - bkL (bkJ p, L)).toNat = 1 := by
      change (L + 1 - L).toNat = 1
      simp
    rw [h1]
    simp
  have hunit : IsUnit (2 : ResidueGroup n) := by
    have : ((2 : ℕ) : ResidueGroup n) = 2 := by norm_num
    rw [← this, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right n (by decide)
  rw [← Int.not_even_iff_odd]
  rintro ⟨k, hk⟩
  -- `k` represents `r(a)`.
  have hk' : ((k : ℤ) : ResidueGroup n) = bkThetaResidue n ξ (bkJ p, L + 1) := by
    apply hunit.mul_left_cancel
    rw [← h2, ← ZMod.coe_valMinAbs (bkThetaResidue n ξ (bkJ p, L)), hk]
    push_cast
    ring
  have hNpos : (0 : ℝ) < ((3 ^ n : ℕ) : ℝ) := by positivity
  obtain ⟨-, hv₁, hv₂⟩ := (ZMod.valMinAbs_spec (bkThetaResidue n ξ (bkJ p, L))
    (bkThetaResidue n ξ (bkJ p, L)).valMinAbs).1 rfl
  rw [hk] at hv₁ hv₂
  have hv₁' : -((3 ^ n : ℕ) : ℝ) < ((k + k : ℤ) : ℝ) * 2 := by exact_mod_cast hv₁
  have hv₂' : ((k + k : ℤ) : ℝ) * 2 ≤ ((3 ^ n : ℕ) : ℝ) := by exact_mod_cast hv₂
  push_cast at hv₁' hv₂'
  have habs : |(k : ℝ)| < ((3 ^ n : ℕ) : ℝ) / 2 := by
    push_cast at hNpos ⊢
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  have hθa : bkTheta n ξ (bkJ p, L + 1) = (k : ℝ) / ((3 ^ n : ℕ) : ℝ) :=
    sfr_eq_of_abs_lt hk' habs
  have hθh : bkTheta n ξ (bkJ p, L) = 2 * ((k : ℝ) / ((3 ^ n : ℕ) : ℝ)) := by
    rw [bkTheta_def, sfr_def, hk]
    push_cast
    ring
  have hblack := hhb.abs_bkTheta_le
  have hw := hwhite.lt_abs_bkTheta
  rw [hθh, abs_mul, abs_two] at hblack
  rw [hθa] at hw
  linarith

/-- **The column top has an odd numerator.** Let `ξ` be a unit, `0 < ε < 1/27` and `p ∈ 𝒫`
black. Then the integer `3^n ϑ(j(p), l_Δ)`, where `l_Δ = l_*(p)` is the second entry of the
canonical triangle `Δ(p)`, is odd. -/
@[collatz_pos_dens "lem_ch_coltop_odd"]
theorem odd_three_pow_mul_bkTheta_bkColTop {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1 / 27) {p : ℤ × ℤ}
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) :
    ∃ N : ℤ, (N : ℝ) = 3 ^ n * bkTheta n ξ (bkJ p, (bkCanonTriangle n ξ ε p hp).l) ∧ Odd N :=
  ⟨_, (three_pow_mul_bkTheta n ξ _).symm,
    odd_valMinAbs_bkThetaResidue_bkColTop hξ hε₀ hε hp hb⟩

end CollatzPosDens
