/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Monotone.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Recipe.Texp

/-!
# The height exponent recurrence `𝓔`

The height exponent recurrence is the function $\mathcal E : \mathbb{N} \to \mathbb{N}$ given by
$$\mathcal E(0) = 0, \qquad
  \mathcal E(j+1) = \mathcal E(j) + K_j + 1 + \mathrm{gr}(b_j),$$
where `b_j = scale j` are the scales, `K_j = cap j = 29 + ⌊j/56⌋` are the overshoot caps and
`gr(u) = texp u = 2u - ⌊19u/12⌋` is the height increment. Since every cap is at least `29`, each
step adds at least `30`.

## Main definitions

* `CollatzPosDens.erec`: the height exponent recurrence `𝓔(j)`.

## Main results

* `CollatzPosDens.erec_zero`, `CollatzPosDens.erec_succ`: the defining equations.
* `CollatzPosDens.erec_succ_eq_add_thirty`: the step with the cap unfolded.
* `CollatzPosDens.erec_strictMono`: `𝓔` is strictly increasing.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The height exponent recurrence `𝓔(j)`: `𝓔(0) = 0` and
`𝓔(j + 1) = 𝓔(j) + K_j + 1 + gr(b_j)`. -/
@[collatz_pos_dens "def_Erec"]
def erec : ℕ → ℕ
  | 0 => 0
  | j + 1 => erec j + cap j + 1 + texp (scale j)

/-- The seed: `𝓔(0) = 0`. -/
@[simp]
theorem erec_zero : erec 0 = 0 := rfl

/-- One step of the recurrence: `𝓔(j + 1) = 𝓔(j) + K_j + 1 + gr(b_j)`. -/
@[simp]
theorem erec_succ (j : ℕ) : erec (j + 1) = erec j + cap j + 1 + texp (scale j) := rfl

/-- One step of the recurrence with the cap unfolded:
`𝓔(j + 1) = 𝓔(j) + 30 + ⌊j/56⌋ + gr(b_j)`. -/
theorem erec_succ_eq_add_thirty (j : ℕ) :
    erec (j + 1) = erec j + 30 + j / 56 + texp (scale j) := by
  rw [erec_succ, cap]; omega

/-- Each step of `𝓔` adds at least `30`. -/
theorem erec_add_thirty_le_succ (j : ℕ) : erec j + 30 ≤ erec (j + 1) := by
  have := twentyNine_le_cap j
  rw [erec_succ]; omega

/-- `𝓔` is strictly increasing. -/
theorem erec_strictMono : StrictMono erec :=
  strictMono_nat_of_lt_succ fun j => by have := erec_add_thirty_le_succ j; omega

/-- `𝓔` is monotone. -/
theorem erec_monotone : Monotone erec :=
  erec_strictMono.monotone

end CollatzPosDens
