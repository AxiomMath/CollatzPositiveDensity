/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factor 41

A kernel-checked lower bound for the factor `j = 41` of the startup product of central masses.
Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, the result bounds `N_41`
below by an explicit natural number, its exact value.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_41`: factor 41.

## Implementation notes

The bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product `prodGo`.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- The factor `j = 41` of the startup product, `prodGo 1 41 (scale 41)`, is at least
`18218552292874671842`. -/
theorem prodGo_block_41 : 18218552292874671842 ≤ prodGo 1 41 (scale 41) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
