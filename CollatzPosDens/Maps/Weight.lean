/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum

/-!
# The weight of a word

For a word `w ∈ 𝕎` of length `d`, its *weight* is the positive rational
`ω(w) = 3 ^ d * 2 ^ (-A(w))`, where `A(w)` is the valuation sum `CollatzPosDens.Word.valSum w`.
The map `R ↦ CollatzPosDens.src w R` is affine with slope `1 / ω(w)`.

## Main definitions

* `CollatzPosDens.Word.weight`: the weight `ω(w) = 3 ^ |w| / 2 ^ A(w)` of a word, in `ℚ`.

## Main results

* `CollatzPosDens.Word.weight_pos`: `0 < ω(w)`.
* `CollatzPosDens.Word.weight_append`: `ω(uv) = ω(u) ω(v)`.
* `CollatzPosDens.Word.weight_cons`: `ω(a w) = (3 / 2 ^ a) ω(w)`.

## Implementation notes

The factor `2 ^ (-A(w))` is written as division by `2 ^ A(w)` with a natural exponent.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

/-- The weight `ω(w) = 3 ^ d * 2 ^ (-A(w))` of a word `w` of length `d`, as a rational. -/
@[collatz_pos_dens "def_weight"]
def weight (w : Word) : ℚ := 3 ^ w.length / 2 ^ valSum w

/-- The empty word has weight `1`. -/
@[simp]
theorem weight_nil : weight [] = 1 := by
  simp [weight]

/-- `ω(a w) = (3 / 2 ^ a) ω(w)`. -/
theorem weight_cons (a : ℕ+) (w : Word) :
    weight (a :: w) = 3 / 2 ^ (a : ℕ) * weight w := by
  simp only [weight, List.length_cons, valSum_cons, pow_succ, pow_add]
  rw [div_mul_div_comm, mul_comm (3 : ℚ)]

/-- A one-letter word `(a)` has weight `3 / 2 ^ a`. -/
theorem weight_singleton (a : ℕ+) : weight [a] = 3 / 2 ^ (a : ℕ) := by
  simp [weight_cons]

/-- The weight is multiplicative under concatenation: `ω(uv) = ω(u) ω(v)`. -/
@[simp]
theorem weight_append (u v : Word) : weight (u ++ v) = weight u * weight v := by
  simp only [weight, List.length_append, valSum_append, pow_add]
  rw [div_mul_div_comm]

/-- The weight of a word is positive. -/
theorem weight_pos (w : Word) : 0 < weight w :=
  div_pos (pow_pos three_pos _) (pow_pos two_pos _)

/-- The weight of a word is nonzero. -/
theorem weight_ne_zero (w : Word) : weight w ≠ 0 :=
  (weight_pos w).ne'

end Word

end CollatzPosDens
