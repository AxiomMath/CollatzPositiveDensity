/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.ZMargin

/-!
# Room below the central-sum margin

The central-sum margin `ε_Z = 2^{-28}` leaves room for two error terms of size `2^{-29}`:
`2^{-29} + 2^{-29} ≤ ε_Z`, with equality.

## Main results

* `CollatzPosDens.two_inv_pow_add_two_inv_pow_le_centralSumMargin`:
  `2^{-29} + 2^{-29} ≤ ε_Z`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Two error terms of size `2^{-29}` together fit within the central-sum margin:
`2^{-29} + 2^{-29} ≤ ε_Z`. -/
@[collatz_pos_dens "lem_Z_margin_room"]
theorem two_inv_pow_add_two_inv_pow_le_centralSumMargin :
    (2 : ℚ)⁻¹ ^ 29 + 2⁻¹ ^ 29 ≤ centralSumMargin := by
  rw [centralSumMargin_def]
  norm_num

end CollatzPosDens
