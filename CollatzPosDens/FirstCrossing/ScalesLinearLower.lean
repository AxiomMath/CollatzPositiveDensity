/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales

/-!
# Linear growth of the scales

The scales `scale j`, given by `scale 0 = 16544` and `scale (j + 1) = scale j + ⌈scale j / 100⌉`,
grow at least linearly: for every `j ∈ ℕ`,
$$\mathrm{scale}(j) \ge 16544 + 166\,j.$$
Indeed every scale is at least `16544`, so each increment is at least `⌈16544/100⌉ = 166`.

## Main results

* `CollatzPosDens.scale_linear_lower`: `16544 + 166 j ≤ scale j` for every `j`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scales grow at least linearly: for every `j ∈ ℕ`, `16544 + 166 j ≤ scale j`. -/
@[collatz_pos_dens "lem_scales_linear_lower"]
theorem scale_linear_lower (j : ℕ) : 16544 + 166 * j ≤ scale j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [scale_succ, eb_eq]
    omega

end CollatzPosDens
