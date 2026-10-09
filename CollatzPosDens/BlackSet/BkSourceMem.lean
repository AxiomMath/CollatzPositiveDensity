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
public import CollatzPosDens.BlackSet.BkColtopSpec
public import CollatzPosDens.BlackSet.BkRowstartSpec
public import CollatzPosDens.BlackSet.BkSizeNonneg

/-!
# A black point lies in its own canonical triangle

Let `ξ` be a unit, `0 < ε < 1/27` and `p = (j, l)` black, with `Δ(p) = (j_*, l_*, s)`.
Then `p ∈ Δ(p)`.

By `CollatzPosDens.not_bkBlack_of_bkDist_le_one`, a black point at distance `1` from a point of
`Δ(p)` lies in `Δ(p)`. The corner `(j_*, l_*)` lies in `Δ(p)` since `s ≥ 0`; the row `l_*` is
black from `j_*` to `j` and the column `j` is black from `l_*` down to `l`, so `p ∈ Δ(p)`.

## Main results

* `CollatzPosDens.mem_bkCanonTriangle_self`: `p ∈ Δ(p)` for a black point `p`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §5.6.
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
  set Δ := bkCanonTriangle n ξ ε p hp with hΔ
  have step : ∀ x y : ℤ × ℤ, x ∈ Δ → y ∈ bkPoints → BkBlack n ξ ε y → bkDist y x = 1 →
      y ∈ Δ := by
    intro x y hx hy hyb hd
    by_contra hyΔ
    exact not_bkBlack_of_bkDist_le_one hξ hε₀ hε hp hb hy hyΔ hx hd.le hyb
  obtain ⟨hjs1, hjsj, hrow, -⟩ := (eq_bkRowStart_iff hp hb (bkRowStart n ξ ε p)).1 rfl
  obtain ⟨hlls, hcol, -⟩ := (eq_bkColTop_iff hξ (by linarith) hp hb (bkColTop n ξ ε p)).1 rfl
  have hcorner : (bkRowStart n ξ ε p, bkColTop n ξ ε p) ∈ Δ :=
    BkTriangle.corner_mem_iff.2 (bkCanonTriangle_s_nonneg hξ hε₀ hp hb)
  have hrowmem : ∀ k : ℤ, bkRowStart n ξ ε p ≤ k → k ≤ bkJ p →
      (k, bkColTop n ξ ε p) ∈ Δ := by
    intro k hk
    induction k, hk using Int.leInduction with
    | base => exact fun _ => hcorner
    | succ k hk ih =>
      intro hkj
      exact step _ _ (ih (by omega)) (mem_bkPoints_mk.2 (by omega))
        (hrow (k + 1) (by omega) hkj) (bkDist_add_one_fst _ _)
  have htop : (bkJ p, bkColTop n ξ ε p) ∈ Δ := hrowmem _ hjsj le_rfl
  have hcolmem : ∀ m : ℤ, m ≤ bkColTop n ξ ε p → bkL p ≤ m → (bkJ p, m) ∈ Δ := by
    intro m hm
    induction m, hm using Int.leInductionDown with
    | base => exact fun _ => htop
    | pred m hm ih =>
      intro hlm
      exact step _ _ (ih (by omega)) (mem_bkPoints_mk.2 hp)
        (hcol (m - 1) hlm (by omega))
        ((bkDist_comm _ _).trans (by simpa using bkDist_add_one_snd _ (m - 1)))
  simpa using hcolmem (bkL p) hlls le_rfl

end CollatzPosDens
