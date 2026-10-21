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
# Claim (*), case 3: points to the left of the canonical triangle

Let `ξ` be a unit, `0 < ε < 1/27`, `p` black with canonical triangle `Δ(p) = (j_*, l_*, s)`,
and let `q ∈ 𝒫` with `q ∉ Δ(p)` be a cardinal neighbour of some `r₀ ∈ Δ(p)`. If
`j(q) < j_*`, then `q` is not black.

As `|j(q) - j(r₀)| + |l(q) - l(r₀)| = 1` and `j(r₀) ≥ j_* > j(q)`, this forces
`j(q) = j_* - 1`, `j(r₀) = j_*` and `l(q) = l(r₀) ≤ l_*`. Since `j_* > j(q) ≥ 1`, the point
`π = (j_* - 1, l_*)` is white by the characterization of the row start. If `q` were black, the
points `(j_*, l(q) + k)` for `1 ≤ k ≤ l_* - l(q)` lie in `Δ(p)` by north-west closure, hence are
black, and upward propagation from `q` along the column `j_* - 1` gives `|ϑ(π)| ≤ ε`,
contradicting that `π` is white.

## Main results

* `CollatzPosDens.not_bkBlack_of_bkJ_lt_bkRowStart`: Claim (*), case 3.

## Implementation notes

The condition `q ∉ Δ(p)` is not assumed: every point of `Δ(p)` has `j ≥ j_*`, so it follows
from `j(q) < j_*`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Claim (*), case 3.** Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black, `q ∈ 𝒫`, and let
`q` be a cardinal neighbour of some `r₀ ∈ Δ(p)`. If `j(q) < j_*(p)`, then `q` is not black.
The condition `q ∉ Δ(p)` follows from `j(q) < j_*(p)` and is not assumed. -/
@[collatz_pos_dens "lem_bk_star_case3"]
theorem not_bkBlack_of_bkJ_lt_bkRowStart {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {p q r₀ : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) (hqP : q ∈ bkPoints)
    (hr₀ : r₀ ∈ bkCanonTriangle n ξ ε p hp) (hcard : BkCardinalNeighbour q r₀)
    (hj : bkJ q < bkRowStart n ξ ε p) :
    ¬BkBlack n ξ ε q := by
  intro hqb
  set js := bkRowStart n ξ ε p
  set ls := bkColTop n ξ ε p
  set Δ := bkCanonTriangle n ξ ε p hp
  have hq1 : 1 ≤ q.1 := hqP
  have hr₀j : js ≤ r₀.1 := hr₀.1
  have hr₀l : r₀.2 ≤ ls := hr₀.2.1
  simp only [BkCardinalNeighbour, bkJ, bkL] at hcard hj
  obtain ⟨hqj, hrj, hql⟩ : q.1 = js - 1 ∧ r₀.1 = js ∧ q.2 = r₀.2 := by
    rcases abs_cases (q.1 - r₀.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (q.2 - r₀.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
  -- The row structure at `p`: `π = (j_* - 1, l_*)` is white.
  have hπw : IsBkWhite n ξ ε (js - 1, ls) :=
    ((eq_bkRowStart_iff hp hb js).1 rfl).2.2.2.resolve_left (by omega)
  -- Upward propagation from `q = (j_* - 1, l(q))` along the column `j_* - 1`.
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
