/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkRowStart
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkNwClosure
public import CollatzPosDens.BlackSet.BkBlackOn
public import CollatzPosDens.BlackSet.BkCardinal
public import CollatzPosDens.BlackSet.BkColtopSpec
public import CollatzPosDens.BlackSet.BkPropLeft
public import CollatzPosDens.BlackSet.BkPropRight
public import CollatzPosDens.BlackSet.BkRowstartSpec

/-!
# Points above the top row of the canonical triangle are not black

Let `ξ` be a unit, `0 < ε < 1/27` and `p` a black point with canonical triangle
`Δ(p) = (j_*, l_*, s)`. Let `q ∉ Δ(p)` lie at distance at most `1` from some `r₀ ∈ Δ(p)`.
If `j(q) ≥ j_*` and `l(q) > l_*`, then `q` is not black.

Since `l(r₀) ≤ l_* < l(q)` and `q, r₀` are cardinal neighbours, `j(q) = j(r₀)`, `l(r₀) = l_*`
and `l(q) = l_* + 1`. If `q` were black, the small angle at `q` would move along the row
`l_* + 1` to `β = (j(p), l_* + 1)`: rightwards over the black stretch `[j_*, j(p)]` of the row
`l_*` when `j(q) < j(p)`, and leftwards when `j(q) > j(p)`, the points `(j(p) + k, l_*)` with
`j(p) + k < j(q)` lying in `Δ(p)` by north-west closure from `r₀`, hence being black. Thus
`|ϑ(β)| ≤ ε`, whereas `β` is white by the characterisation of the column top `l_*(p)`.

## Main results

* `CollatzPosDens.not_bkBlack_of_bkRowStart_le_of_bkColTop_lt`: a point `q` within distance `1`
  of `Δ(p)` with `j(q) ≥ j_*` and `l(q) > l_*` is not black.

## Implementation notes

The hypothesis `q ∈ 𝒫` of [mazur2026] is not assumed: it follows from `j(q) ≥ j_* ≥ 1`. The
hypothesis `q ∉ Δ(p)` is kept, as in [mazur2026], although it is implied by `l(q) > l_*` and is
not used. Black points are points of `𝒫`, which is recorded by the hypothesis `p ∈ bkPoints`
(needed to form `Δ(p)`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black, `q ∉ Δ(p)`, and let `r₀ ∈ Δ(p)` with
`|q - r₀| ≤ 1`. If `j(q) ≥ j_*(p)` and `l(q) > l_*(p)`, then `q` is not black. -/
@[collatz_pos_dens "lem_bk_star_case2"]
theorem not_bkBlack_of_bkRowStart_le_of_bkColTop_lt {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {p q r₀ : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (_hq : q ∉ bkCanonTriangle n ξ ε p hp)
    (hr₀ : r₀ ∈ bkCanonTriangle n ξ ε p hp) (hdist : bkDist q r₀ ≤ 1)
    (hj : bkRowStart n ξ ε p ≤ bkJ q) (hl : bkColTop n ξ ε p < bkL q) :
    ¬BkBlack n ξ ε q := by
  intro hqb
  set js := bkRowStart n ξ ε p
  set ls := bkColTop n ξ ε p
  set Δ := bkCanonTriangle n ξ ε p hp
  have hΔj : Δ.j = js := rfl
  have hΔl : Δ.l = ls := rfl
  have hr₀j : js ≤ bkJ r₀ := hΔj ▸ BkTriangle.j_le_of_mem hr₀
  have hr₀l : bkL r₀ ≤ ls := hΔl ▸ BkTriangle.le_l_of_mem hr₀
  have hqr : q ≠ r₀ := by
    rintro rfl
    omega
  have hcard := abs_bkJ_sub_add_abs_bkL_sub_eq_one hqr hdist
  obtain ⟨hqj, hr₀l', hql⟩ : bkJ q = bkJ r₀ ∧ bkL r₀ = ls ∧ bkL q = ls + 1 := by
    rcases abs_cases (bkJ q - bkJ r₀) with h1 | h1 <;>
      rcases abs_cases (bkL q - bkL r₀) with h2 | h2 <;> omega
  obtain ⟨hpl, -, hwhite⟩ := (eq_bkColTop_iff hξ (by linarith) hp hb ls).1 rfl
  obtain ⟨hjs1, hjsp, hrow, -⟩ := (eq_bkRowStart_iff hp hb js).1 rfl
  have hqeq : q = (bkJ q, ls + 1) := Prod.ext rfl hql
  have hθq : |bkTheta n ξ (bkJ q, ls + 1)| ≤ ε := hqeq ▸ hqb.2
  have hβ : |bkTheta n ξ (bkJ p, ls + 1)| ≤ ε := by
    rcases lt_trichotomy (bkJ q) (bkJ p) with hlt | heq | hgt
    · have h := abs_bkTheta_add_right_le n ξ (j := bkJ q) (l := ls + 1)
        (mem_bkPoints_mk.2 (by omega)) (bkJ p - bkJ q).toNat (by linarith) hθq
        fun k hk hkm => by
          rw [add_sub_cancel_right]
          exact (hrow _ (by omega) (by omega)).2
      rwa [show bkJ q + ((bkJ p - bkJ q).toNat : ℤ) = bkJ p by omega] at h
    · rwa [← heq]
    · refine abs_bkTheta_le_of_row_east n ξ (j := bkJ p) (l := ls + 1)
        (mem_bkPoints_mk.2 (by omega)) (bkJ q - bkJ p).toNat (by linarith) ?_ fun k hk => ?_
      · rwa [show bkJ p + ((bkJ q - bkJ p).toNat : ℤ) = bkJ q by omega]
      · rw [add_sub_cancel_right]
        have hmem : ((bkJ p + k, ls) : ℤ × ℤ) ∈ Δ :=
          BkTriangle.mem_of_mem_of_nw hr₀
            (hΔj ▸ hjsp.trans (le_add_of_nonneg_right (Int.natCast_nonneg k)))
            (by simp only [bkJ] at *; omega) (by simp only [bkL] at *; omega)
            (by rw [hΔl])
        exact (bkBlack_of_mem_bkCanonTriangle hξ hε₀ hε hp hb hmem).2
  exact (hβ.trans_lt hwhite.2).false

end CollatzPosDens
