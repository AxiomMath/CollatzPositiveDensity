/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.BlackSet.BkColtopSpec
public import CollatzPosDens.BlackSet.BkEpsStarRange

/-!
# Gaps of vertically adjacent black points

Let `ξ : ResidueGroup n` be a unit and `ε < 1/4`. If `(j, l) ∈ bkPoints` and `(j, l + 1)` are
both black, then `trGap n ξ ε (j, l) = trGap n ξ ε (j, l + 1) + 1`. Indeed, let
`L = bkColTop n ξ ε (j, l + 1)`; by `eq_bkColTop_iff` at `(j, l + 1)`, the point `(j, l'')` is
black for `l + 1 ≤ l'' ≤ L` and `(j, L + 1)` is white, so, `(j, l)` being black too,
`eq_bkColTop_iff` at `(j, l)` gives `bkColTop n ξ ε (j, l) = L`. Since
`bkColTop n ξ ε p = l(p) + trGap n ξ ε p` (`bkColTop_eq_add_trGap`), this is
`l + trGap n ξ ε (j, l) = l + 1 + trGap n ξ ε (j, l + 1)`.

## Main results

* `CollatzPosDens.trGap_eq_trGap_add_one_of_bkBlack_of_bkBlack`: the identity, for a general
  colour scale `ε < 1/4`.
* `CollatzPosDens.trGap_eq_trGap_add_one_of_bkBlack_of_bkBlack_epsStar`: the identity at the
  colour scale `ε = epsStar`.

## Implementation notes

The identity is usually stated at `ε = epsStar` with `n ≥ 1`; the argument uses only `ε < 1/4`
(which `epsStar` satisfies) and not `n ≥ 1`, so the main statement is proved under these weaker
hypotheses, and the case `ε = epsStar` is a corollary.

## References

* [Mazur, *Collatz positive density*], §9.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Gaps of vertically adjacent black points.** Let `ξ` be a unit and `ε < 1/4`. If
`(j, l) ∈ 𝒫` and `(j, l + 1)` are both black, then `gap((j, l)) = gap((j, l + 1)) + 1`. -/
@[collatz_pos_dens "lem_tr_gap_adjacent"]
theorem trGap_eq_trGap_add_one_of_bkBlack_of_bkBlack {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {ε : ℝ} (hε : ε < 1 / 4) {j l : ℤ} (hp : (j, l) ∈ bkPoints)
    (hb : BkBlack n ξ ε (j, l)) (hb' : BkBlack n ξ ε (j, l + 1)) :
    trGap n ξ ε (j, l) = trGap n ξ ε (j, l + 1) + 1 := by
  have hp' : (j, l + 1) ∈ bkPoints := by
    rw [mem_bkPoints] at hp ⊢
    exact hp
  set L := bkColTop n ξ ε (j, l + 1)
  obtain ⟨hlL, hblack, hwhite⟩ := (eq_bkColTop_iff hξ hε hp' hb' L).mp rfl
  have hL0 : L = bkColTop n ξ ε (j, l) := by
    refine (eq_bkColTop_iff hξ hε hp hb L).mpr ⟨?_, ?_, hwhite⟩
    · change l + 1 ≤ L at hlL
      change l ≤ L
      omega
    intro l'' h1 h2
    simp only [bkL, bkJ] at h1 h2 hblack ⊢
    rcases h1.eq_or_lt with rfl | h1
    · exact hb
    · exact hblack l'' (by omega) h2
  have e1 := bkColTop_eq_add_trGap n ξ ε (j, l)
  have e2 := bkColTop_eq_add_trGap n ξ ε (j, l + 1)
  simp only [bkL] at e1 e2
  omega

/-- **Gaps of vertically adjacent black points**, at the colour scale `ε_*`. -/
theorem trGap_eq_trGap_add_one_of_bkBlack_of_bkBlack_epsStar {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {j l : ℤ} (hp : (j, l) ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) (j, l)) (hb' : BkBlack n ξ (epsStar : ℝ) (j, l + 1)) :
    trGap n ξ (epsStar : ℝ) (j, l) = trGap n ξ (epsStar : ℝ) (j, l + 1) + 1 :=
  trGap_eq_trGap_add_one_of_bkBlack_of_bkBlack hξ
    (epsStar_mem_bkRange.2.trans (by norm_num)) hp hb hb'

end CollatzPosDens
