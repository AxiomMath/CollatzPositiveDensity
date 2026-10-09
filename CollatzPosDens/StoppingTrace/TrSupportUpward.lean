/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.Renewal.RnPascal

/-!
# Live blocks climb

Let `β = (c, e)` be a block, with `c = (c₁, …, c_m)` and closing letter `e ∈ {4, 5}`. If its
weight `bw(β) = ϖ(e) ∏ᵢ [cᵢ ∉ {4, 5}] ϖ(cᵢ)` is nonzero, then every factor is nonzero, so
`ϖ(cᵢ) ≠ 0`, i.e. `cᵢ ≥ 2`, for every `i`. Hence the second coordinate of the block point is
`l(β) = c₁ + ⋯ + c_m + e ≥ 2m + e ≥ 4`.

## Main results

* `CollatzPosDens.two_mul_length_add_le_bkL_chBlockPoint`: a block `(c, e)` of nonzero
  weight has `l(β) ≥ 2|c| + e`.
* `CollatzPosDens.four_le_bkL_chBlockPoint_of_chBlockWeight_ne_zero`: a block of nonzero
  weight whose closing letter is `4` or `5` has `l(β) ≥ 4`.

## Implementation notes

Blocks are modelled as `List ℤ × ℤ`, as for `chBlockPoint` and `chBlockWeight`, and `l(β)` is
`bkL (chBlockPoint β)`. Membership in `𝔅 = ℤ^{<ω} × {4, 5}` is needed only through the bound
`e ≥ 4`, so the main result assumes `4 ≤ β.2`, which generalizes the source.

## References

* [Mazur, *Collatz positive density*], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- A block `β = (c, e)` of nonzero weight satisfies `l(β) ≥ 2|c| + e`. -/
theorem two_mul_length_add_le_bkL_chBlockPoint {β : List ℤ × ℤ} (hβ : chBlockWeight β ≠ 0) :
    2 * (β.1.length : ℤ) + β.2 ≤ bkL (chBlockPoint β) := by
  have := two_mul_length_le_sum_of_chBlockWeight_ne_zero hβ
  simp only [bkL, chBlockPoint_snd]
  omega

/-- **Live blocks climb.** If a block `β = (c, e)` with closing letter `e ≥ 4` (in particular
`β ∈ 𝔅`, i.e. `e ∈ {4, 5}`) has `bw(β) ≠ 0`, then `l(β) ≥ 4`. -/
@[collatz_pos_dens "lem_tr_support_upward"]
theorem four_le_bkL_chBlockPoint_of_chBlockWeight_ne_zero {β : List ℤ × ℤ} (he : 4 ≤ β.2)
    (hβ : chBlockWeight β ≠ 0) : 4 ≤ bkL (chBlockPoint β) := by
  have := two_mul_length_add_le_bkL_chBlockPoint hβ
  omega

end CollatzPosDens
