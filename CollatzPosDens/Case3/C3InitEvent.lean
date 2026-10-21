/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Xo
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# The initial deviation set

For a Fourier index `ι ∈ 𝔍` and `g ∈ ℕ`, the initial deviation set `𝓘_g(ι) ⊆ ℤ × ℤ` consists
of the pairs `(r, ℓ)` whose overshoot is large, `ℓ - g ≥ X_o(ι)`, or whose horizontal coordinate
is far from its mean, `|r - g/4| ≥ g/32`. Here `X_o(ι)` is the overshoot allowance
`overshootAllowance ι`.

## Main definitions

* `CollatzPosDens.c3InitEvent ι g`: the initial deviation set `𝓘_g(ι)`.

## Main results

* `CollatzPosDens.mem_c3InitEvent`: the defining characterisation of `(r, ℓ) ∈ 𝓘_g(ι)`.
* `CollatzPosDens.mem_c3InitEvent_iff_int`: the same characterisation in integer arithmetic,
  `ℓ - g ≥ X_o(ι)` or `g ≤ |32 r - 8 g|`.

## Implementation notes

The horizontal condition `|r - g/4| ≥ g/32` is stated in `ℝ`;
`mem_c3InitEvent_iff_int` clears the denominators.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The initial deviation set `𝓘_g(ι)`: the pairs `(r, ℓ) ∈ ℤ × ℤ` with `ℓ - g ≥ X_o(ι)` or
`|r - g/4| ≥ g/32`. -/
@[collatz_pos_dens "def_c3_init_event"]
def c3InitEvent (ι : FIndex) (g : ℕ) : Set (ℤ × ℤ) :=
  {p | (overshootAllowance ι : ℤ) ≤ p.2 - g ∨ (g : ℝ) / 32 ≤ |(p.1 : ℝ) - g / 4|}

/-- The defining characterisation of `(r, ℓ) ∈ 𝓘_g(ι)`. -/
lemma mem_c3InitEvent {ι : FIndex} {g : ℕ} {r ℓ : ℤ} :
    (r, ℓ) ∈ c3InitEvent ι g ↔
      (overshootAllowance ι : ℤ) ≤ ℓ - g ∨ (g : ℝ) / 32 ≤ |(r : ℝ) - g / 4| :=
  Iff.rfl

/-- The horizontal condition `|r - g/4| ≥ g/32` is `g ≤ |32 r - 8 g|` in integers. -/
lemma div_le_abs_sub_div_iff_int {g : ℕ} {r : ℤ} :
    (g : ℝ) / 32 ≤ |(r : ℝ) - g / 4| ↔ (g : ℤ) ≤ |32 * r - 8 * g| := by
  have h : |(r : ℝ) - g / 4| = |((32 * r - 8 * g : ℤ) : ℝ)| / 32 := by
    push_cast
    rw [show (32 * (r : ℝ) - 8 * g) = 32 * (r - g / 4) by ring, abs_mul]
    norm_num
  rw [h, div_le_div_iff_of_pos_right (by norm_num), ← Int.cast_abs,
    show ((g : ℝ)) = ((g : ℤ) : ℝ) by norm_cast, Int.cast_le]

/-- The characterisation of `(r, ℓ) ∈ 𝓘_g(ι)` in integer arithmetic:
`ℓ - g ≥ X_o(ι)` or `g ≤ |32 r - 8 g|`. -/
lemma mem_c3InitEvent_iff_int {ι : FIndex} {g : ℕ} {r ℓ : ℤ} :
    (r, ℓ) ∈ c3InitEvent ι g ↔
      (overshootAllowance ι : ℤ) ≤ ℓ - g ∨ (g : ℤ) ≤ |32 * r - 8 * g| := by
  rw [mem_c3InitEvent, div_le_abs_sub_div_iff_int]

end CollatzPosDens
