/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Case3.C3Tip
public import CollatzPosDens.Case3.C3Bridge
public import CollatzPosDens.BlackSet.BkDisjoint
public import CollatzPosDens.BlackSet.BkEpsStarRange

/-!
# New triangles have tips above the old top

Let `ξ` be a unit, and let `Δ₀ ≠ Δ'` be members of the canonical family
`𝔗 = 𝔗_{n,ξ,ε_*}`. Let `(j₀, l₀) ∈ Δ₀`, `g ∈ ℕ` with `l₀ + g = l_{Δ₀}`, and `(j, l) ∈ Δ'` with
`l_{Δ₀} ≤ l ≤ l_{Δ₀} + W` and `|j - (j₀ + g / 4)| ≤ J_e`, where `J_e + α W + 1 ≤ g δ₀`.
Then `l_{Δ₀} ≤ tip(Δ')`.

If instead `tip(Δ') < l_{Δ₀}`, then `BkTriangle.exists_mem_mem_of_tip_lt` produces a point
common to `Δ₀` and `Δ'`. As `0 < ε_* < 1/27`, the canonical family is disjoint
(`eq_of_mem_bkFamily_of_mem`), so `Δ₀ = Δ'`, a contradiction.

## Main results

* `CollatzPosDens.le_tip_of_mem_bkFamily`: the statement for `𝔗_{n,ξ,ε}` with any
  `0 < ε < 1/27`.
* `CollatzPosDens.le_tip_of_mem_bkFamily_epsStar`: the statement at `ε = ε_*`.

## Implementation notes

The conditions `W, J_e ≥ 0` follow from the other hypotheses (`l_{Δ₀} ≤ l ≤ l_{Δ₀} + W` and
`0 ≤ |j - (j₀ + g / 4)| ≤ J_e`), so they are not assumed. `W` and `J_e` are real numbers. No
assumption `n ≥ 1` is needed.
-/

@[expose] public section

namespace CollatzPosDens

/-- The tip bound for the canonical family `𝔗_{n,ξ,ε}` with `ξ` a unit and `0 < ε < 1/27`. -/
theorem le_tip_of_mem_bkFamily {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hξ : IsResidueUnit ξ) (hε : 0 < ε) (hε' : ε < 1 / 27) {Δ₀ Δ' : BkTriangle}
    (hΔ₀ : Δ₀ ∈ bkFamily n ξ ε) (hΔ' : Δ' ∈ bkFamily n ξ ε) (hne : Δ₀ ≠ Δ')
    {j₀ l₀ j l : ℤ} {g : ℕ} {W Je : ℝ}
    (h₀ : (j₀, l₀) ∈ Δ₀) (hg : l₀ + g = Δ₀.l) (h' : (j, l) ∈ Δ') (hl₁ : Δ₀.l ≤ l)
    (hl₂ : (l : ℝ) ≤ Δ₀.l + W) (hj : |(j : ℝ) - (j₀ + g / 4)| ≤ Je)
    (hE : Je + alpha * W + 1 ≤ g * drift) :
    (Δ₀.l : ℝ) ≤ Δ'.tip := by
  by_contra htip
  obtain ⟨jb, -, hb₀, hb'⟩ :=
    BkTriangle.exists_mem_mem_of_tip_lt h₀ hg h' hl₁ hl₂ hj hE (lt_of_not_ge htip)
  exact hne (eq_of_mem_bkFamily_of_mem hξ hε hε' hΔ₀ hΔ' hb₀ hb')

/-- Let `ξ` be a unit, `Δ₀ ≠ Δ'` members of `𝔗 = 𝔗_{n,ξ,ε_*}`, `(j₀, l₀) ∈ Δ₀`, `g ∈ ℕ` with
`l₀ + g = l_{Δ₀}`, and `(j, l) ∈ Δ'` with `l_{Δ₀} ≤ l ≤ l_{Δ₀} + W` and
`|j - (j₀ + g / 4)| ≤ J_e`, where `J_e + α W + 1 ≤ g δ₀`. Then `l_{Δ₀} ≤ tip(Δ')`. -/
@[collatz_pos_dens "lem_c3_close"]
theorem le_tip_of_mem_bkFamily_epsStar {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {Δ₀ Δ' : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) (hΔ' : Δ' ∈ bkFamily n ξ epsStar)
    (hne : Δ₀ ≠ Δ') {j₀ l₀ j l : ℤ} {g : ℕ} {W Je : ℝ}
    (h₀ : (j₀, l₀) ∈ Δ₀) (hg : l₀ + g = Δ₀.l) (h' : (j, l) ∈ Δ') (hl₁ : Δ₀.l ≤ l)
    (hl₂ : (l : ℝ) ≤ Δ₀.l + W) (hj : |(j : ℝ) - (j₀ + g / 4)| ≤ Je)
    (hE : Je + alpha * W + 1 ≤ g * drift) :
    (Δ₀.l : ℝ) ≤ Δ'.tip :=
  le_tip_of_mem_bkFamily hξ epsStar_mem_bkRange.1
    epsStar_mem_bkRange.2 hΔ₀ hΔ' hne h₀ hg h' hl₁ hl₂ hj hE

end CollatzPosDens
