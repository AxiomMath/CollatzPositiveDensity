/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkClaimStar
public import CollatzPosDens.BlackSet.BkCardinal
public import CollatzPosDens.BlackSet.BkNeighbourhood
public import CollatzPosDens.BlackSet.BkColtopSpec
public import CollatzPosDens.BlackSet.BkRowstartSpec
public import CollatzPosDens.BlackSet.BkSizeNonneg

/-!
# A black point lies in its own canonical triangle

Let `ξ` be a unit, `0 < ε < 1/27` and `p = (j, l)` black, with `Δ(p) = (j_*, l_*, s)`.
Then `p ∈ Δ(p)`.

By Claim (*), a black cardinal neighbour of a point of `Δ(p)` lies in `Δ(p)`: otherwise it
would lie in the cardinal neighbourhood `𝒩(Δ(p))`, none of whose points is black. The corner
`(j_*, l_*)` lies in `Δ(p)` since `s ≥ 0`; walking right along the row `l_*` (all black by the
characterization of `j_*`) reaches `(j, l_*)`, and walking down the column `j` (all black by the
characterization of `l_*`) reaches `(j, l) = p`.

## Main results

* `CollatzPosDens.mem_bkCanonTriangle_self`: `p ∈ Δ(p)` for a black point `p`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **A black point lies in its canonical triangle.** Let `ξ` be a unit, `0 < ε < 1/27` and
`p ∈ 𝒫` black. Then `p ∈ Δ(p)`. -/
@[collatz_pos_dens "lem_bk_source_mem"]
theorem mem_bkCanonTriangle_self {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) :
    p ∈ bkCanonTriangle n ξ ε p hp := by
  set Δ := bkCanonTriangle n ξ ε p hp
  -- Black cardinal neighbours of points of `Δ(p)` lie in `Δ(p)`.
  have step : ∀ x y : ℤ × ℤ, x ∈ Δ → y ∈ bkPoints → BkBlack n ξ ε y →
      BkCardinalNeighbour y x → y ∈ Δ := by
    intro x y hx hy hyb hyx
    by_contra hyΔ
    exact not_bkBlack_of_bkDist_le_one hξ hε₀ hε hp hb
      (mem_bkNeighbourhood_of hy hyΔ hx hyx) hyb
  obtain ⟨hjs1, hjsj, hrow, -⟩ := (eq_bkRowStart_iff hp hb (bkRowStart n ξ ε p)).1 rfl
  obtain ⟨hlls, hcol, -⟩ := (eq_bkColTop_iff hξ (by linarith) hp hb (bkColTop n ξ ε p)).1 rfl
  -- Walk right along the row `l_*`.
  have hrowmem : ∀ k : ℤ, bkRowStart n ξ ε p ≤ k → k ≤ bkJ p →
      (k, bkColTop n ξ ε p) ∈ Δ := by
    intro k hk
    induction k, hk using Int.leInduction with
    | base => exact fun _ => BkTriangle.corner_mem_iff.2 (bkCanonTriangle_s_nonneg hξ hε₀ hp hb)
    | succ k hk ih =>
      intro hkj
      exact step _ _ (ih (by omega)) (mem_bkPoints_mk.2 (by omega))
        (hrow (k + 1) (by omega) hkj) (by simp [bkCardinalNeighbour_iff, bkJ, bkL])
  -- Walk down the column `j`.
  have hcolmem : ∀ m : ℤ, m ≤ bkColTop n ξ ε p → bkL p ≤ m → (bkJ p, m) ∈ Δ := by
    intro m hm
    induction m, hm using Int.leInductionDown with
    | base => exact fun _ => hrowmem _ hjsj le_rfl
    | pred m hm ih =>
      intro hlm
      exact step _ _ (ih (by omega)) (mem_bkPoints_mk.2 hp)
        (hcol (m - 1) hlm (by omega)) (by simp [bkCardinalNeighbour_iff, bkJ, bkL])
  simpa using hcolmem (bkL p) hlls le_rfl

end CollatzPosDens
