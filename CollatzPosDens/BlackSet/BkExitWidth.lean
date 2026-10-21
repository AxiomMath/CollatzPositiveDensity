/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import CollatzPosDens.Attr

/-!
# The exit width `f_s = ⌊(5s + 16) / 16⌋`

For `s ∈ ℕ` the exit width is the positive integer `f_s := ⌊(5s + 16) / 16⌋`. Since `5 / 16`
is a lower bound for the slope `α = log 2 / log 9`, this is a lower bound for `⌊α s⌋ + 1`.

## Main definitions

* `CollatzPosDens.bkExitWidth`: the exit width `f_s = ⌊(5s + 16) / 16⌋`.

## Main results

* `CollatzPosDens.bkExitWidth_eq_floor`: `f_s` is the floor of the real number `(5s + 16) / 16`.
* `CollatzPosDens.one_le_bkExitWidth`: `1 ≤ f_s`.
* `CollatzPosDens.bkExitWidth_le_succ`: `f_s ≤ s + 1`.
* `CollatzPosDens.bkExitWidth_le_two_pow`: `f_s ≤ 2 ^ s`.

## Implementation notes

The exit width is a natural number computed with truncating division on `ℕ`, which agrees
with the floor of the rational quotient (`bkExitWidth_eq_floor`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The exit width `f_s := ⌊(5s + 16) / 16⌋`, a positive integer. -/
@[collatz_pos_dens "def_bk_exit_width"]
def bkExitWidth (s : ℕ) : ℕ := (5 * s + 16) / 16

/-- Unfolding lemma for `bkExitWidth`. -/
lemma bkExitWidth_def (s : ℕ) : bkExitWidth s = (5 * s + 16) / 16 := rfl

/-- `f_s = ⌊(5s + 16) / 16⌋` in any linearly ordered semifield with a floor. -/
lemma bkExitWidth_eq_floor {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorSemiring K] (s : ℕ) :
    bkExitWidth s = ⌊(5 * s + 16 : K) / 16⌋₊ := by
  rw [bkExitWidth_def, ← Nat.floor_div_eq_div (K := K)]
  push_cast
  rfl

/-- `f_s = ⌊5s / 16⌋ + 1`. -/
lemma bkExitWidth_eq_add_one (s : ℕ) : bkExitWidth s = 5 * s / 16 + 1 := by
  rw [bkExitWidth_def]; omega

/-- The exit width is at least `1`. -/
lemma one_le_bkExitWidth (s : ℕ) : 1 ≤ bkExitWidth s := by
  rw [bkExitWidth_def]; omega

/-- The exit width is positive. -/
lemma bkExitWidth_pos (s : ℕ) : 0 < bkExitWidth s := one_le_bkExitWidth s

/-- `16 f_s ≤ 5s + 16`. -/
lemma sixteen_mul_bkExitWidth_le (s : ℕ) : 16 * bkExitWidth s ≤ 5 * s + 16 := by
  rw [bkExitWidth_def]; omega

/-- `5s < 16 f_s`. -/
lemma five_mul_lt_sixteen_mul_bkExitWidth (s : ℕ) : 5 * s < 16 * bkExitWidth s := by
  rw [bkExitWidth_def]; omega

/-- The exit width is monotone in `s`. -/
lemma bkExitWidth_mono : Monotone bkExitWidth := fun a b h => by
  simp only [bkExitWidth_def]; omega

/-- `f_s ≤ s + 1`. -/
lemma bkExitWidth_le_succ (s : ℕ) : bkExitWidth s ≤ s + 1 := by
  rw [bkExitWidth_def]; omega

/-- `f_s ≤ 2 ^ s`. -/
lemma bkExitWidth_le_two_pow (s : ℕ) : bkExitWidth s ≤ 2 ^ s :=
  (bkExitWidth_le_succ s).trans Nat.lt_two_pow_self

end CollatzPosDens
