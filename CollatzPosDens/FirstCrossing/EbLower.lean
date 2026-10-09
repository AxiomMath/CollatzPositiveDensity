/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Lower bound for the scale increment `e_b`

For every `b ∈ ℕ` the scale increment satisfies `e_b ≥ max(1, b/100)`. For `b ≤ 12` this is
`e_b = 1`; for `b ≥ 13` every candidate value of `e_b` is an integer `k ≥ ⌈b/100⌉ ≥ 1`.

## Main results

* `CollatzPosDens.eb_ge_ceil_div_hundred`: `⌈b/100⌉ = (b + 99) / 100 ≤ e_b`.
* `CollatzPosDens.eb_lower`: `max 1 (b / 100) ≤ e_b` in `ℝ`.

## Implementation notes

The natural-number ceiling `⌈b/100⌉` is written `(b + 99) / 100`, matching the definition of
`eb`. The bound `e_b ≥ ⌈b/100⌉` holds for every `b`, since `⌈b/100⌉ ≤ 1` for `b ≤ 12`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `e_b ≥ ⌈b/100⌉`, with the ceiling written as `(b + 99) / 100`. -/
theorem eb_ge_ceil_div_hundred (b : ℕ) : (b + 99) / 100 ≤ eb b := by
  unfold eb
  split_ifs with h₁ h₂
  · omega
  · obtain ⟨_, k, hkb, hk, hkp⟩ := h₂
    exact (Nat.findGreatest_spec (P := fun k => (b + 99) / 100 ≤ k ∧
      9 * 3 ^ b * 16 ^ k < 4 ^ (b + 1)) hkb ⟨hk, hkp⟩).1
  · exact le_rfl

/-- For every `b ∈ ℕ`, `e_b ≥ max(1, b/100)`. -/
@[collatz_pos_dens "lem_eb_lower"]
theorem eb_lower (b : ℕ) : max 1 ((b : ℝ) / 100) ≤ eb b := by
  refine max_le (by exact_mod_cast one_le_eb b) ?_
  rw [div_le_iff₀ (by norm_num)]
  have := eb_ge_ceil_div_hundred b
  exact_mod_cast (by omega : b ≤ eb b * 100)

end CollatzPosDens
