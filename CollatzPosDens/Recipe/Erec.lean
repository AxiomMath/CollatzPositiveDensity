/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Monotone.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Recipe.Texp

/-!
# The height exponent recurrence `𝓔`

The height exponent recurrence is the function $\mathcal E : \mathbb{N} \to \mathbb{N}$ given by
$$\mathcal E(0) = 0, \qquad
  \mathcal E(j+1) = \mathcal E(j) + 17 + \lfloor j/32 \rfloor + \mathrm t(\beta(j)),$$
where `β(j)` is `CollatzPosDens.scale j` and `t(u) = 2u - ⌊19u/12⌋` is `CollatzPosDens.texp u`.

## Main definitions

* `CollatzPosDens.erec`: the height exponent recurrence `𝓔(j)`.

## Main results

* `CollatzPosDens.erec_zero`, `CollatzPosDens.erec_succ`: the defining equations.
* `CollatzPosDens.erec_strictMono`: `𝓔` is strictly increasing.
* `CollatzPosDens.seventeen_mul_le_erec`: `17 j ≤ 𝓔(j)`.

## Implementation notes

The floor `⌊j/32⌋` is natural-number division `j / 32`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The height exponent recurrence `𝓔(j)`: `𝓔(0) = 0` and
`𝓔(j + 1) = 𝓔(j) + 17 + ⌊j/32⌋ + texp (scale j)`. -/
@[collatz_pos_dens "def_Erec"]
def erec : ℕ → ℕ
  | 0 => 0
  | j + 1 => erec j + 17 + j / 32 + texp (scale j)

/-- The seed: `𝓔(0) = 0`. -/
@[simp]
theorem erec_zero : erec 0 = 0 := rfl

/-- One step of the recurrence: `𝓔(j + 1) = 𝓔(j) + 17 + ⌊j/32⌋ + t(β(j))`. -/
@[simp]
theorem erec_succ (j : ℕ) : erec (j + 1) = erec j + 17 + j / 32 + texp (scale j) := rfl

/-- Each step of `𝓔` adds at least `17`. -/
theorem erec_add_seventeen_le_succ (j : ℕ) : erec j + 17 ≤ erec (j + 1) := by
  rw [erec_succ]; omega

/-- `𝓔` is strictly increasing. -/
theorem erec_strictMono : StrictMono erec :=
  strictMono_nat_of_lt_succ fun j => by have := erec_add_seventeen_le_succ j; omega

/-- `𝓔` is monotone. -/
theorem erec_monotone : Monotone erec :=
  erec_strictMono.monotone

/-- `𝓔` grows at least linearly: `17 j ≤ 𝓔(j)`. -/
theorem seventeen_mul_le_erec (j : ℕ) : 17 * j ≤ erec j := by
  induction j with
  | zero => simp
  | succ j ih => have := erec_add_seventeen_le_succ j; omega

end CollatzPosDens
