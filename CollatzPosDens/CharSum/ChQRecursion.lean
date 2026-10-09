/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChQHorizon
public import CollatzPosDens.CharSum.ChQfiniteStep

/-!
# The renewal recursion for `Q`

Fix a level `n`, a residue `ξ : ResidueGroup n` and a threshold `ε`, and write
`Q = chQ n ξ ε`, `w = chWhiteFactor n ξ ε`, `bw = chBlockWeight`,
`I = chInternalWeight n ξ ε` and `bpt = chBlockPoint`. For every point `p ∈ bkPoints`,
`Q(p) = w(p) ∑_{β ∈ 𝔅} bw(β) I(p; β) Q(p + bpt(β))`,
where `𝔅` is the alphabet of blocks. Indeed, with `J = n / 2` and `j = bkJ`, since
`J ≤ j(p) + (J + 1)`, the value `Q(p)` equals the finite-horizon product
`chQFinite n ξ ε (J + 1) p`; its step recursion expresses it through the products
`chQFinite n ξ ε J (p + bpt(β))`, and these are `Q(p + bpt(β))` by definition.

## Main results

* `CollatzPosDens.chQ_eq_mul_tsum_of_nonneg`: the recursion under the hypothesis
  `0 ≤ j(p)`.
* `CollatzPosDens.chQ_eq_mul_tsum`: for `p ∈ bkPoints`,
  `Q(p) = w(p) ∑_{β ∈ 𝔅} bw(β) I(p; β) Q(p + bpt(β))`.

## Implementation notes

The alphabet `𝔅` is the subtype of pairs `List ℤ × ℤ` whose closing letter lies in `{4, 5}`,
and the sum over `𝔅` is a `tsum`, as in `CollatzPosDens.chQFinite_succ`. The hypothesis
`p ∈ bkPoints` is used only through `0 ≤ j(p)`.

## References

* [Mazur, *Collatz positive density*], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The renewal recursion for `Q` at any base point `p` with `0 ≤ bkJ p`. -/
theorem chQ_eq_mul_tsum_of_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {p : ℤ × ℤ}
    (hp : 0 ≤ bkJ p) :
    chQ n ξ ε p =
      chWhiteFactor n ξ ε p *
        ∑' β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
          chBlockWeight β * chInternalWeight n ξ ε p β * chQ n ξ ε (p + chBlockPoint β) := by
  have hK : ((n / 2 : ℕ) : ℤ) ≤ bkJ p + ((n / 2 + 1 : ℕ) : ℤ) := by
    push_cast
    omega
  rw [chQ_eq_chQFinite_of_nonneg n ξ ε hp hK, chQFinite_succ]
  rfl

/-- **Renewal recursion for `Q`.** For `p ∈ bkPoints`,
`Q(p) = w(p) ∑_{β ∈ 𝔅} bw(β) I(p; β) Q(p + bpt(β))`. -/
@[collatz_pos_dens "lem_ch_Q_recursion"]
theorem chQ_eq_mul_tsum (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {p : ℤ × ℤ}
    (hp : p ∈ bkPoints) :
    chQ n ξ ε p =
      chWhiteFactor n ξ ε p *
        ∑' β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
          chBlockWeight β * chInternalWeight n ξ ε p β * chQ n ξ ε (p + chBlockPoint β) :=
  chQ_eq_mul_tsum_of_nonneg n ξ ε (by have := mem_bkPoints.mp hp; omega)

end CollatzPosDens
