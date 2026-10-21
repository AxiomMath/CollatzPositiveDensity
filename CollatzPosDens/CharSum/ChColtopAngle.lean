/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkCornerValue
public import CollatzPosDens.BlackSet.BkSeBound
public import CollatzPosDens.BlackSet.BkSourceMem

/-!
# The angle on the top row of the canonical triangle

Let `ξ` be a unit, `0 < ε < 1/27` and `p` a black point with canonical triangle
`Δ(p) = (j_Δ, l_Δ, s_Δ)`, and write `l(p) + ω = l_Δ` with `ω ∈ ℕ`. Then the angle at the
point `(j(p), l_Δ)` of the top row of `Δ(p)` above `p` satisfies
`|ϑ(j(p), l_Δ)| ≤ ε 2^{-ω}`.

Indeed `p ∈ Δ(p)`, so `j(p) ≥ j_Δ` and `(j(p) - j_Δ) log 9 + ω log 2 ≤ s_Δ`. Moving from the
corner `c = (j_Δ, l_Δ)` east to `h = (j(p), l_Δ)` costs `se(c, h) = (j(p) - j_Δ) log 9`, so
`|ϑ(h)| ≤ e^{se(c, h)} |ϑ(c)| = ε e^{se(c, h) - s_Δ} ≤ ε e^{-ω log 2} = ε 2^{-ω}`.

## Main results

* `CollatzPosDens.abs_bkTheta_colTop_le`: `|ϑ(j(p), l_Δ)| ≤ ε 2^{-ω}`.

## References

* [Mazur, *Collatz positive density*], §6.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The angle on the top row of the canonical triangle.** Let `ξ` be a unit,
`0 < ε < 1/27`, `p ∈ 𝒫` black with canonical triangle `Δ(p) = (j_Δ, l_Δ, s_Δ)`, and `ω ∈ ℕ`
with `l(p) + ω = l_Δ`. Then `|ϑ(j(p), l_Δ)| ≤ ε 2^{-ω}`. -/
@[collatz_pos_dens "lem_ch_coltop_angle"]
theorem abs_bkTheta_colTop_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (ω : ℕ)
    (hω : bkL p + ω = (bkCanonTriangle n ξ ε p hp).l) :
    |bkTheta n ξ (bkJ p, (bkCanonTriangle n ξ ε p hp).l)| ≤ ε * (2 : ℝ) ^ (-(ω : ℤ)) := by
  set Δ := bkCanonTriangle n ξ ε p hp with hΔ
  have hmem := mem_bkCanonTriangle_self hξ hε₀ hε hp hb
  rw [← hΔ] at hmem
  obtain ⟨hj, -, hw⟩ := BkTriangle.mem_iff.1 hmem
  have hωl : Δ.l - bkL p = ω := by omega
  rw [hωl] at hw
  have hse := abs_bkTheta_le_exp_bkSe_mul n ξ Δ.corner_mem_bkPoints
    (q := (bkJ p, Δ.l)) (mem_bkPoints_mk.2 (Δ.one_le_j.trans hj)) hj le_rfl
  have hc := abs_bkTheta_bkCanonTriangle_corner hξ hε₀ hp hb
  rw [← hΔ] at hc
  rw [hc] at hse
  refine hse.trans ?_
  have h2 : (2 : ℝ) ^ (-(ω : ℤ)) = Real.exp (-((ω : ℝ) * Real.log 2)) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num)]
    push_cast
    ring_nf
  rw [h2, mul_left_comm, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hε₀.le
  simp only [bkSe, BkTriangle.corner, bkJ, bkL, sub_self, Int.cast_zero, zero_mul,
    add_zero] at hw ⊢
  push_cast at hw ⊢
  linarith

end CollatzPosDens
