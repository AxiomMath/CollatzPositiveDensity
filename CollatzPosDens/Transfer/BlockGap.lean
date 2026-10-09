/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.Beta
public import CollatzPosDens.Transfer.Bitlength

/-!
# The block gap of the scale schedule

For all `k, p ∈ ℕ`,
`4096 · 136 · (min(p, 2^{k+1} - 2) + 1) < β_*(2^k - 1)`.
Indeed `β_*(2^k - 1) ≥ K_* 2^k`, while the left side is below `4096 · 272 · 2^k`, and
`K_* = 9863028149 > 4096 · 272`.

## Main results

* `CollatzPosDens.betaStar_block_gap`: the block gap inequality.

## Implementation notes

The subtractions `2^k - 1` and `2^{k+1} - 2` are truncated subtractions in `ℕ`; since
`2^k ≥ 1` and `2^{k+1} ≥ 2` they agree with the integer ones.
-/

@[expose] public section

namespace CollatzPosDens

/-- The block gap: `4096 · 136 · (min(p, 2^{k+1} - 2) + 1) < β_*(2^k - 1)` for all `k, p`. -/
@[collatz_pos_dens "lem_s02_block_gap"]
theorem betaStar_block_gap (k p : ℕ) :
    4096 * 136 * (min p (2 ^ (k + 1) - 2) + 1) < betaStar (2 ^ k - 1) := by
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hβ := Kstar_mul_le_betaStar (2 ^ k - 1)
  rw [Nat.sub_add_cancel hk, Kstar_eq] at hβ
  have hmin : min p (2 ^ (k + 1) - 2) + 1 < 2 * 2 ^ k := by
    rw [pow_succ]; omega
  omega

end CollatzPosDens
