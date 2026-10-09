/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.Pinit
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Iterate

/-!
# The schedule positions `p_i`

For `i : ℕ`, the `i`-th schedule position is `p_i := 𝔤^i(p_init)`, the `i`-fold composition of
the recipe map `𝔤` applied to the initial time `p_init = 1024`, with `𝔤^0 = id`. Thus
`p_0 = p_init` and `p_{i+1} = 𝔤(p_i)`. Since `𝔤` is strictly inflationary, the schedule is
strictly increasing.

## Main definitions

* `CollatzPosDens.schedule`: the schedule position `p_i = 𝔤^[i] p_init`.

## Main results

* `CollatzPosDens.schedule_zero`: `p_0 = p_init`.
* `CollatzPosDens.schedule_succ`: `p_{i+1} = 𝔤(p_i)`.
* `CollatzPosDens.schedule_zero_add_one`: `p_0 + 1 = 1025`.
* `CollatzPosDens.schedule_lt_schedule_succ`: `p_i < p_{i+1}`.
* `CollatzPosDens.schedule_strictMono`: `i ↦ p_i` is strictly increasing.
* `CollatzPosDens.schedule_monotone`: `i ↦ p_i` is monotone.
* `CollatzPosDens.pInit_le_schedule`: `p_init ≤ p_i`.

## Implementation notes

The `i`-fold composition is Mathlib's `Nat.iterate`, written `recipeMap^[i]`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The schedule position `p_i := 𝔤^i(p_init)`. -/
@[collatz_pos_dens "def_s02_schedule"]
noncomputable def schedule (i : ℕ) : ℕ := recipeMap^[i] pInit

/-- The schedule position `p_i` is the `i`-fold iterate of the recipe map at `p_init`. -/
theorem schedule_def (i : ℕ) : schedule i = recipeMap^[i] pInit := rfl

/-- The initial schedule position is `p_0 = p_init`. -/
@[simp]
theorem schedule_zero : schedule 0 = pInit := rfl

/-- Each schedule position is the recipe map applied to the previous one: `p_{i+1} = 𝔤(p_i)`. -/
theorem schedule_succ (i : ℕ) : schedule (i + 1) = recipeMap (schedule i) :=
  Function.iterate_succ_apply' recipeMap i pInit

/-- `p_0 + 1 = 1025`, since `p_init = 1024`. -/
theorem schedule_zero_add_one : schedule 0 + 1 = 1025 := rfl

/-- Consecutive schedule positions strictly increase: `p_i < p_{i+1}`. -/
theorem schedule_lt_schedule_succ (i : ℕ) : schedule i < schedule (i + 1) := by
  rw [schedule_succ]; exact lt_recipeMap _

/-- The schedule `i ↦ p_i` is strictly increasing. -/
theorem schedule_strictMono : StrictMono schedule :=
  strictMono_nat_of_lt_succ schedule_lt_schedule_succ

/-- The schedule `i ↦ p_i` is monotone. -/
theorem schedule_monotone : Monotone schedule := schedule_strictMono.monotone

/-- Every schedule position is at least the initial time: `p_init ≤ p_i`. -/
theorem pInit_le_schedule (i : ℕ) : pInit ≤ schedule i :=
  schedule_zero ▸ schedule_monotone (Nat.zero_le i)

end CollatzPosDens
