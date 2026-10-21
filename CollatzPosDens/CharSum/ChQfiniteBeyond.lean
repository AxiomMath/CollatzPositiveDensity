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
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChQfinite

/-!
# The finite-horizon white products beyond the cut-off

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and let `J = ⌊n/2⌋`. If `j(p) > J`,
then every block path point `p + Bp_i(β)` has first coordinate at least `j(p) > J`, and every
point at which an internal weight `I(p + Bp_{k-1}(β); βᵏ)` evaluates a residual reward has first
coordinate at least `j(p) + 1 > J`. None of these points is white, so every white factor equals
`1`; and at each of them the residual reward `ρ_c = R_c - [c ∈ {4, 5}] [white]` is `0 - 0`, since
the paid reward vanishes beyond `J`, so every internal weight equals `1`. Hence `Q^{(K)}(p)` is the
total mass
`∑_{β ∈ 𝔅^K} ∏_k bw(βᵏ) = 1`.

## Main results

* `CollatzPosDens.chQFinite_eq_one_of_lt_bkJ`: if `j(p) > ⌊n/2⌋` then `Q^{(K)}(p) = 1` for
  every `K ∈ ℕ`.

## Implementation notes

The base point `p` ranges over all of `ℤ × ℤ`; the hypothesis `p ∈ 𝒫` is not needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Finite-horizon products beyond the cut-off.** If `j(p) > ⌊n/2⌋`, then
`Q^{(K)}(p) = 1` for every `K ∈ ℕ`. -/
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
  rw [Finset.prod_eq_one fun i _ ↦ chWhiteFactor_of_not_isBkWhite fun hw ↦
      (hw.bkJ_le.trans_lt (hp.trans_le (hge _ i))).false,
    Finset.prod_eq_one fun k _ ↦ chInternalWeight_eq_one_of_le ξ ε
      (by exact hp.le.trans (hge _ _)) _]
  ring

end CollatzPosDens
