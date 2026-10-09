/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factors 0 to 5, 6 to 11, 12 to 17, 18 to 23

Kernel-checked lower bounds for blocks of consecutive factors of the startup product of central
masses. Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, each result gives
an explicit natural number below `∏_{j₀ ≤ j < j₀ + n} N_j`: the exact value when `n = 1`, and
otherwise a `63`-bit mantissa times a power of two.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_0`: factors 0 to 5.
* `CollatzPosDens.fcStartupProduct.prodGo_block_6`: factors 6 to 11.
* `CollatzPosDens.fcStartupProduct.prodGo_block_12`: factors 12 to 17.
* `CollatzPosDens.fcStartupProduct.prodGo_block_18`: factors 18 to 23.

## Implementation notes

Each bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product `prodGo`.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- Certificate block for the factors `0 ≤ j ≤ 5`. -/
theorem prodGo_block_0 : 5191936660356582311 * 2 ^ 314 ≤ prodGo 6 0 (scale 0) := by
  decide +kernel

/-- Certificate block for the factors `6 ≤ j ≤ 11`. -/
theorem prodGo_block_6 : 5852268257217917209 * 2 ^ 317 ≤ prodGo 6 6 (scale 6) := by
  decide +kernel

/-- Certificate block for the factors `12 ≤ j ≤ 17`. -/
theorem prodGo_block_12 : 6137128244975270897 * 2 ^ 318 ≤ prodGo 6 12 (scale 12) := by
  decide +kernel

/-- Certificate block for the factors `18 ≤ j ≤ 23`. -/
theorem prodGo_block_18 : 6632768685339916734 * 2 ^ 319 ≤ prodGo 6 18 (scale 18) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
