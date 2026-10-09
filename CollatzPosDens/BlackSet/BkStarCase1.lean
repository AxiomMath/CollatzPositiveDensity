/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkSeExact
public import CollatzPosDens.BlackSet.BkCardinal
public import CollatzPosDens.BlackSet.BkCornerValue

/-!
# Neighbours of a canonical triangle below and to the right of its corner are not black

Let `ξ` be a unit, `0 < ε < 1/18`, `p` black with canonical triangle `Δ(p) = (j_*, l_*, s)` and
corner `c = (j_*, l_*)`. Suppose `q ∉ Δ(p)` lies within distance `1` of some `r₀ ∈ Δ(p)`. If
`j(q) ≥ j_*` and `l(q) ≤ l_*`, then `q` is not black.

Since `q ≠ r₀`, the two points are cardinal neighbours, so `D = se(c, q)` exceeds
`se(c, r₀) ≤ s` by at most `log 9`. On the other hand `q ∉ Δ(p)` forces `D > s`. The corner
value `|ϑ(c)| = ε e^{-s}` gives `e^D |ϑ(c)| = ε e^{D - s} ≤ 9ε < 1/2`, so the angle scales
exactly and `|ϑ(q)| = ε e^{D - s} > ε`.

## Main results

* `CollatzPosDens.not_bkBlack_of_bkRowStart_le_of_le_bkColTop`: a point `q ∉ Δ(p)` within
  distance `1` of `Δ(p)` with `j(q) ≥ j_*` and `l(q) ≤ l_*` is not black.

## Implementation notes

The hypothesis `q ∈ 𝒫` is not assumed: it follows from `j(q) ≥ j_* ≥ 1`. The argument only
needs `9ε < 1/2`, so the statement is made under `ε < 1/18` rather than `ε < 1/27`.

## References

* [Mazur, §5.5]
-/

@[expose] public section

namespace CollatzPosDens

/-- Moving to a cardinal neighbour raises the weight `se(c, ·)` by at most `log 9`. -/
theorem bkSe_sub_bkSe_le_log_nine {c q r : ℤ × ℤ} (hqr : q ≠ r) (hdist : bkDist q r ≤ 1) :
    bkSe c q - bkSe c r ≤ Real.log 9 := by
  have hcard := abs_bkJ_sub_add_abs_bkL_sub_eq_one hqr hdist
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog29 : Real.log 2 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
  rw [show bkSe c q - bkSe c r = ((bkJ q - bkJ r : ℤ) : ℝ) * Real.log 9 -
      ((bkL q - bkL r : ℤ) : ℝ) * Real.log 2 by
    simp only [bkSe, Int.cast_sub]
    ring]
  generalize bkJ q - bkJ r = x at hcard
  generalize bkL q - bkL r = y at hcard
  obtain ⟨hx, hxy⟩ : x ≤ 1 ∧ x - y ≤ 1 := by
    rcases abs_cases x with h | h <;> rcases abs_cases y with h' | h' <;> omega
  nlinarith [mul_le_mul_of_nonneg_right (by exact_mod_cast hx : (x : ℝ) ≤ 1)
      (sub_nonneg.2 hlog29),
    mul_le_mul_of_nonneg_right (by exact_mod_cast hxy : (x : ℝ) - y ≤ 1) hlog2]

/-- Let `ξ` be a unit, `0 < ε < 1/18`, `p ∈ 𝒫` black, `q ∉ Δ(p)`, and let `r₀ ∈ Δ(p)` with
`|q - r₀| ≤ 1`. If `j(q) ≥ j_*(p)` and `l(q) ≤ l_*(p)`, then `q` is not black. -/
@[collatz_pos_dens "lem_bk_star_case1"]
theorem not_bkBlack_of_bkRowStart_le_of_le_bkColTop {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {p q r₀ : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 18)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (hq : q ∉ bkCanonTriangle n ξ ε p hp)
    (hr₀ : r₀ ∈ bkCanonTriangle n ξ ε p hp) (hdist : bkDist q r₀ ≤ 1)
    (hj : bkRowStart n ξ ε p ≤ bkJ q) (hl : bkL q ≤ bkColTop n ξ ε p) :
    ¬BkBlack n ξ ε q := by
  set Δ := bkCanonTriangle n ξ ε p hp
  set c := Δ.corner
  have hF2 : bkSe c r₀ ≤ Δ.s := BkTriangle.bkSe_corner_le_of_mem hr₀
  have hD : Δ.s < bkSe c q := not_le.1 fun h => hq (BkTriangle.mem_iff_bkSe.2 ⟨hj, hl, h⟩)
  have hDr : bkSe c q - bkSe c r₀ ≤ Real.log 9 :=
    bkSe_sub_bkSe_le_log_nine (fun h => hq (h ▸ hr₀)) hdist
  have hval : Real.exp (bkSe c q) * |bkTheta n ξ c| = ε * Real.exp (bkSe c q - Δ.s) := by
    rw [abs_bkTheta_bkCanonTriangle_corner hξ hε₀ hp hb, sub_eq_add_neg, Real.exp_add]
    ring
  have hsmall : Real.exp (bkSe c q) * |bkTheta n ξ c| < 1 / 2 := by
    rw [hval]
    calc ε * Real.exp (bkSe c q - Δ.s)
        ≤ ε * Real.exp (Real.log 9) := by
          gcongr
          linarith
      _ = 9 * ε := by rw [Real.exp_log (by norm_num), mul_comm]
      _ < 1 / 2 := by linarith
  apply not_bkBlack_of_lt
  rw [abs_bkTheta_eq_exp_bkSe_mul n ξ Δ.one_le_j (mem_bkPoints.2 (Δ.one_le_j.trans hj)) hj hl
    hsmall, hval]
  exact lt_mul_of_one_lt_right hε₀ (Real.one_lt_exp_iff.2 (sub_pos.2 hD))

end CollatzPosDens
