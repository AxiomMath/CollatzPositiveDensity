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
public import CollatzPosDens.BlackSet.BkNwClosure
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkBlackOn
public import CollatzPosDens.BlackSet.BkCardinal
public import CollatzPosDens.BlackSet.BkPropUp
public import CollatzPosDens.BlackSet.BkRowstartSpec

/-!
# Points to the left of the canonical triangle are not black

Let `ξ` be a unit, `0 < ε < 1/27`, `p` black with canonical triangle `Δ(p) = (j_*, l_*, s)`,
and let `q ∈ 𝒫` with `q ∉ Δ(p)` lie at distance at most `1` from some `r₀ ∈ Δ(p)`. If
`j(q) < j_*`, then `q` is not black.

Since `q ≠ r₀`, the two points are cardinal neighbours; as `j(r₀) ≥ j_* > j(q)`, this forces
`j(q) = j_* - 1`, `j(r₀) = j_*` and `l(q) = l(r₀) ≤ l_*`. Since `j_* > j(q) ≥ 1`, the point
`π = (j_* - 1, l_*)` is white by the characterization of the row start. If `q` were black, the
points `(j_*, l(q) + k)` for `1 ≤ k ≤ l_* - l(q)` lie in `Δ(p)` by north-west closure, hence are
black, and upward propagation from `q` along the column `j_* - 1` gives `|ϑ(π)| ≤ ε`,
contradicting that `π` is white.

## Main results

* `CollatzPosDens.not_bkBlack_of_bkJ_lt_bkRowStart`: a point outside the canonical triangle
  `Δ(p)` of a black point `p`, adjacent to `Δ(p)` and lying in a column `j < j_*`, is not black.

## References

* [Mazur, §5.5]
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black, `q ∈ 𝒫` with `q ∉ Δ(p)`, and let
`r₀ ∈ Δ(p)` with `|q - r₀| ≤ 1`. If `j(q) < j_*(p)`, then `q` is not black. -/
@[collatz_pos_dens "lem_bk_star_case3"]
theorem not_bkBlack_of_bkJ_lt_bkRowStart {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {p q r₀ : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (hqP : q ∈ bkPoints)
    (hq : q ∉ bkCanonTriangle n ξ ε p hp)
    (hr₀ : r₀ ∈ bkCanonTriangle n ξ ε p hp) (hdist : bkDist q r₀ ≤ 1)
    (hj : bkJ q < bkRowStart n ξ ε p) :
    ¬BkBlack n ξ ε q := by
  intro hqb
  set js := bkRowStart n ξ ε p
  set ls := bkColTop n ξ ε p
  set Δ := bkCanonTriangle n ξ ε p hp
  have hq1 : 1 ≤ q.1 := hqP
  have hcard := abs_bkJ_sub_add_abs_bkL_sub_eq_one (fun h : q = r₀ => hq (h ▸ hr₀)) hdist
  have hr₀j : js ≤ r₀.1 := hr₀.1
  have hr₀l : r₀.2 ≤ ls := hr₀.2.1
  simp only [bkJ, bkL] at hcard hj
  obtain ⟨hqj, hrj, hql⟩ : q.1 = js - 1 ∧ r₀.1 = js ∧ q.2 = r₀.2 := by
    rcases abs_cases (q.1 - r₀.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (q.2 - r₀.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
  have hπw : IsBkWhite n ξ ε (js - 1, ls) :=
    ((eq_bkRowStart_iff hp hb js).1 rfl).2.2.2.resolve_left (by omega)
  have hgP : (js - 1, q.2) ∈ bkPoints := mem_bkPoints_mk.2 (by omega)
  have h₀ : |bkTheta n ξ (js - 1, q.2)| ≤ ε := by
    rw [← hqj]
    exact hqb.2
  have hup := abs_bkTheta_add_le_of_east n ξ (ls - q.2).toNat hgP (by linarith) h₀
    fun k hk hkm => by
      rw [sub_add_cancel]
      have hy : (js, q.2 + (k : ℤ)) ∈ Δ :=
        BkTriangle.mem_of_mem_of_nw hr₀ (q' := (js, q.2 + (k : ℤ))) le_rfl
          (by simp only [bkJ]; omega) (by simp only [bkL]; omega)
          (by simp only [bkL]; change _ ≤ ls; omega)
      exact (bkBlack_of_mem_bkCanonTriangle hξ hε₀ hε hp hb hy).2
  rw [show q.2 + ((ls - q.2).toNat : ℤ) = ls by omega] at hup
  exact (hup.trans_lt hπw.2).false

end CollatzPosDens
