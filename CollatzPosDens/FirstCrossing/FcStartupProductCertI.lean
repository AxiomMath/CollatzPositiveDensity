/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factor 40

A kernel-checked lower bound for the factor `j = 40` of the startup product of central masses.
Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, the result gives the exact
value of `N_40` as a natural number bound for `prodGo 1 40 (scale 40)`.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_40`: the lower bound
  `18156354835146418379 ≤ prodGo 1 40 (scale 40)`.

## Implementation notes

The bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product `prodGo`. The kernel's memory use grows with the scale `b_40`, so this factor
is checked on its own.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- A lower bound for the factor `j = 40` of the startup product: `prodGo 1 40 (scale 40)` is at
least `18156354835146418379`. -/
theorem prodGo_block_40 : 18156354835146418379 ≤ prodGo 1 40 (scale 40) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
