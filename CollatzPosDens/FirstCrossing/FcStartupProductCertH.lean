/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factor 39

A kernel-checked lower bound for the factor `j = 39` of the startup product of central masses.
Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, the result states the exact
value of `N_39` as an explicit natural number.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_39`: the lower bound
  `18068291912358912937 ≤ prodGo 1 39 (scale 39)`.

## Implementation notes

The bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product `prodGo`. The kernel's memory use grows with the scale `b_39`, so this factor
is checked on its own.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- A lower bound for the factor `j = 39` of the startup product: `prodGo 1 39 (scale 39)` is at
least `18068291912358912937`. -/
theorem prodGo_block_39 : 18068291912358912937 ≤ prodGo 1 39 (scale 39) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
