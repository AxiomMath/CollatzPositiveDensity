/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChRaw3Factor
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChQfinite

/-!
# The finite-horizon white products beyond the cut-off

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and let `J = ⌊n/2⌋`. If `j(p) > J`,
then every block path point `p + Bp_i(β)` has first coordinate at least `j(p) > J`, and every
point `p + Bp_{k-1}(β) + (i, c₁ + ⋯ + c_i)` at which an internal weight evaluates a raw-three
factor has first coordinate at least `j(p) + 1 > J`. None of these points is white, so all
white and raw-three factors equal `1`, and `Q^{(K)}(p)` is the total mass
`∑_{β ∈ 𝔅^K} ∏_k bw(βᵏ) = 1`.

## Main results

* `CollatzPosDens.chQFinite_eq_one_of_lt_bkJ`: if `j(p) > ⌊n/2⌋` then `Q^{(K)}(p) = 1` for
  every `K ∈ ℕ`.
* `CollatzPosDens.chQFinite_eq_one_of_lt_bkJ_chInternalWeight`: an internal weight started
  at a point `x` with `j(x) ≥ ⌊n/2⌋` equals `1`.

## Implementation notes

The base point `p` ranges over all of `ℤ × ℤ`: no hypothesis `p ∈ 𝒫` is imposed.

## References

* [Mazur, *Collatz positive density*], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- An internal weight started at a point `x` with `j(x) ≥ ⌊n/2⌋` equals `1`: every point at
which it evaluates a raw-three factor has first coordinate `> ⌊n/2⌋`, so is not white. -/
theorem chQFinite_eq_one_of_lt_bkJ_chInternalWeight {n : ℕ} (ξ : ResidueGroup n) (ε : ℝ)
    {x : ℤ × ℤ} (hx : ((n / 2 : ℕ) : ℤ) ≤ bkJ x) (β : List ℤ × ℤ) :
    chInternalWeight n ξ ε x β = 1 := by
  refine Finset.prod_eq_one fun i _ ↦ chRaw3Factor_of_not_isBkWhite fun hw ↦ ?_
  have := hw.bkJ_le
  simp only [bkJ, Prod.fst_add] at this hx
  omega

/-- If `j(p) > ⌊n/2⌋`, then `Q^{(K)}(p) = 1` for every `K ∈ ℕ`. -/
@[collatz_pos_dens "lem_ch_Qfinite_beyond"]
theorem chQFinite_eq_one_of_lt_bkJ (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ)
    {p : ℤ × ℤ} (hp : ((n / 2 : ℕ) : ℤ) < bkJ p) : chQFinite n ξ ε K p = 1 := by
  have hge : ∀ (γ : List (List ℤ × ℤ)) (i : ℕ), bkJ p ≤ bkJ (p + chBlockPath γ i) := by
    intro γ i
    have := chBlockPath_fst_nonneg γ i
    simp only [bkJ, Prod.fst_add]
    omega
  rw [chQFinite_eq_tsum, ← tsum_prod_chBlockWeight K]
  refine tsum_congr fun β ↦ ?_
  unfold chQFiniteTerm
  rw [Finset.prod_eq_one fun i _ ↦ chWhiteFactor_of_not_isBkWhite fun hw ↦ by
      have := hw.bkJ_le; have := hge (List.ofFn fun k ↦ (β k).1) i; omega,
    Finset.prod_eq_one fun k _ ↦ chQFinite_eq_one_of_lt_bkJ_chInternalWeight ξ ε
      (by have := hge (List.ofFn fun k ↦ (β k).1) k; omega) _]
  ring

end CollatzPosDens
