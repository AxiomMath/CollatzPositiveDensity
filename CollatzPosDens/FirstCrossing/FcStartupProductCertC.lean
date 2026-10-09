/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factors 42 to 90, 91 to 139

Kernel-checked lower bounds for blocks of consecutive factors of the startup product of central
masses. Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, each result gives
an explicit natural number below `∏_{j₀ ≤ j < j₀ + n} N_j`: the exact value when `n = 1`, and
otherwise a `63`-bit mantissa times a power of two.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_42`: factors 42 to 90.
* `CollatzPosDens.fcStartupProduct.prodGo_block_91`: factors 91 to 139.

## Implementation notes

Each bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product `prodGo`.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- A lower bound for the product of the factors `42 ≤ j ≤ 90` of the startup product. -/
theorem prodGo_block_42 : 7217030509734483734 * 2 ^ 3073 ≤ prodGo 49 42 (scale 42) := by
  decide +kernel

/-- A lower bound for the product of the factors `91 ≤ j ≤ 139` of the startup product. -/
theorem prodGo_block_91 : 9049828183239844139 * 2 ^ 3073 ≤ prodGo 49 91 (scale 91) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
