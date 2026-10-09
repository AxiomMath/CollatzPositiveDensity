/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb

/-!
# The power inequality for the scale increment `e_b`

For every integer `13 ≤ b ≤ 255` the scale increment satisfies `9 · 3^b · 16^(e_b) < 4^(b+1)`.
Indeed, for each such `b` the integer comparison `9 · 3^b · 16^⌈b/100⌉ < 4^(b+1)` holds, and
`⌈b/100⌉ ≤ b`, so the candidate set in the definition of `e_b` is nonempty; `e_b` is then its
greatest element and in particular satisfies the defining inequality.

## Main results

* `CollatzPosDens.eb_power`: `9 · 3^b · 16^(e_b) < 4^(b+1)` for `13 ≤ b ≤ 255`.
* `CollatzPosDens.eb_power_ceil`: `9 · 3^b · 16^⌈b/100⌉ < 4^(b+1)` for `13 ≤ b ≤ 255`.

## Implementation notes

The comparison at `k = ⌈b/100⌉ = (b + 99) / 100` is verified for all `243` values of `b` by
kernel evaluation of a bounded universal statement over `ℕ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `13 ≤ b ≤ 255`, `9 · 3^b · 16^⌈b/100⌉ < 4^(b+1)`, with `⌈b/100⌉ = (b + 99) / 100`. -/
theorem eb_power_ceil {b : ℕ} (hb₁ : 13 ≤ b) (hb₂ : b ≤ 255) :
    9 * 3 ^ b * 16 ^ ((b + 99) / 100) < 4 ^ (b + 1) := by
  have key : ∀ b < 256, 13 ≤ b → 9 * 3 ^ b * 16 ^ ((b + 99) / 100) < 4 ^ (b + 1) := by
    decide +kernel
  exact key b (by omega) hb₁

/-- **Power inequality for `e_b`.** For every integer `13 ≤ b ≤ 255`,
`9 · 3^b · 16^(e_b) < 4^(b+1)`. -/
@[collatz_pos_dens "lem_eb_power"]
theorem eb_power {b : ℕ} (hb₁ : 13 ≤ b) (hb₂ : b ≤ 255) :
    9 * 3 ^ b * 16 ^ eb b < 4 ^ (b + 1) :=
  (eb_isGreatest hb₁ hb₂ ⟨(b + 99) / 100, le_rfl, by omega, eb_power_ceil hb₁ hb₂⟩).1.2.2

end CollatzPosDens
