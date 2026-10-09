/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.BlackSet.BkCanonEdge
public import CollatzPosDens.BlackSet.BkInset

/-!
# The right edge of the canonical family

Let `ξ : ResidueGroup n` be a unit, `0 < ε < 1/27` and `Δ ∈ bkFamily n ξ ε`. Then
`Δ.j + Δ.s / log 9 < n / 2 - 1/2`: every triangle of the canonical family `bkFamily n ξ ε`
ends strictly more than half a column to the left of `n / 2`.

Write `Δ` as the canonical triangle `bkCanonTriangle` of a black point `p`. The exact edge of a
canonical triangle gives `Δ.j + Δ.s / log 9 ≤ n / 2 + 1 - log (1/ε) / log 9`, and
`log (1/ε) / log 9 > 3/2` for `0 < ε < 1/27`.

## Main results

* `CollatzPosDens.j_add_s_div_log_nine_lt_of_mem_bkFamily`:
  `Δ.j + Δ.s / log 9 < n / 2 - 1/2` for `Δ ∈ bkFamily n ξ ε`.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {Δ : BkTriangle}

/-- **Right edge of the canonical family.** Let `ξ` be a unit, `0 < ε < 1/27` and
`Δ ∈ bkFamily n ξ ε`. Then `Δ.j + Δ.s / log 9 < n / 2 - 1/2`. -/
@[collatz_pos_dens "lem_bk_right_edge"]
theorem j_add_s_div_log_nine_lt_of_mem_bkFamily (hξ : IsResidueUnit ξ) (hε : 0 < ε)
    (hε' : ε < 1 / 27) (hΔ : Δ ∈ bkFamily n ξ ε) :
    (Δ.j : ℝ) + Δ.s / Real.log 9 < (n : ℝ) / 2 - 1 / 2 := by
  obtain ⟨p, hp, hb, rfl⟩ := hΔ
  have h1 := bkCanonTriangle_j_add_s_div_log_nine_le hξ hε hp hb
  have h2 := three_halves_lt_log_inv_div_log_nine hε hε'
  linarith

end CollatzPosDens
