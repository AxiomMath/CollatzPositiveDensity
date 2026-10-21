/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapUpper

/-!
# The grid majorant `Ū_c(θ)` of the capped packet factor

For an integer `c` and a rational `θ`, the grid majorant is
`Ū_c(θ) = min (1, max (U^{10^{-18}}_c(θ), 1526 / 10^8))` if `3 ≤ c ≤ 16`, and `Ū_c(θ) = 1`
otherwise, where `U^η_c` is the rational majorant `CollatzPosDens.trCapUpper` with the rounding
mesh `η = 10^{-18}`. The lower clip `1526 / 10^8` is `2^{-16}` rounded up to the mesh `10^{-8}`.

Since `U^η_c(θ)` already lies in `[1526 / 10^8, 1]` for `3 ≤ c ≤ 16` and equals `1` otherwise,
the clipping changes nothing: `Ū_c(θ) = U^{10^{-18}}_c(θ)`.

## Main definitions

* `CollatzPosDens.c3H17CapUp`: the grid majorant `Ū_c(θ)`.

## Main results

* `CollatzPosDens.c3H17CapUp_of_mem`, `CollatzPosDens.c3H17CapUp_of_not_mem`: the two cases.
* `CollatzPosDens.c3H17CapUp_eq_trCapUpper`: `Ū_c(θ) = U^{10^{-18}}_c(θ)`.
* `CollatzPosDens.c3H17CapUp_le_one`, `CollatzPosDens.c3H17CapUp_pos`,
  `CollatzPosDens.c3H17CapUp_nonneg`: `0 < Ū_c(θ) ≤ 1`.
* `CollatzPosDens.le_c3H17CapUp`: `1526 / 10^8 ≤ Ū_c(θ)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The grid majorant `Ū_c(θ)` of the capped packet factor:
`min (1, max (U^{10^{-18}}_c(θ), 1526 / 10^8))` if `3 ≤ c ≤ 16`, and `1` otherwise. -/
@[collatz_pos_dens "def_c3_h17_cap_up"]
def c3H17CapUp (c : ℤ) (θ : ℚ) : ℚ :=
  if 3 ≤ c ∧ c ≤ 16 then min 1 (max (trCapUpper c (1 / 10 ^ 18) θ) (1526 / 10 ^ 8)) else 1

/-- For `3 ≤ c ≤ 16`, `Ū_c(θ) = min (1, max (U^{10^{-18}}_c(θ), 1526 / 10^8))`. -/
theorem c3H17CapUp_of_mem {c : ℤ} (h₁ : 3 ≤ c) (h₂ : c ≤ 16) (θ : ℚ) :
    c3H17CapUp c θ = min 1 (max (trCapUpper c (1 / 10 ^ 18) θ) (1526 / 10 ^ 8)) :=
  ite_eq_left_of_eq_true _ _ (eq_true ⟨h₁, h₂⟩)

/-- Outside `3 ≤ c ≤ 16`, `Ū_c(θ) = 1`. -/
theorem c3H17CapUp_of_not_mem {c : ℤ} (h : ¬(3 ≤ c ∧ c ≤ 16)) (θ : ℚ) :
    c3H17CapUp c θ = 1 :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

/-- The rational majorant `U^η_c(θ)` is at least `1526 / 10^8`. -/
theorem le_trCapUpper (c : ℤ) (η θ : ℚ) : (1526 / 10 ^ 8 : ℚ) ≤ trCapUpper c η θ := by
  unfold trCapUpper
  split_ifs
  · refine le_min (by norm_num) ?_
    gcongr
    exact_mod_cast le_max_right _ _
  · norm_num

/-- The clipping is vacuous: `Ū_c(θ) = U^{10^{-18}}_c(θ)`. -/
theorem c3H17CapUp_eq_trCapUpper (c : ℤ) (θ : ℚ) :
    c3H17CapUp c θ = trCapUpper c (1 / 10 ^ 18) θ := by
  unfold c3H17CapUp
  split_ifs with h
  · rw [max_eq_left (le_trCapUpper _ _ _), min_eq_right (trCapUpper_le_one _ _ _)]
  · exact (trCapUpper_of_not_mem h _ _).symm

/-- The grid majorant satisfies `Ū_c(θ) ≤ 1`. -/
theorem c3H17CapUp_le_one (c : ℤ) (θ : ℚ) : c3H17CapUp c θ ≤ 1 := by
  rw [c3H17CapUp_eq_trCapUpper]
  exact trCapUpper_le_one _ _ _

/-- The grid majorant satisfies `1526 / 10^8 ≤ Ū_c(θ)`. -/
theorem le_c3H17CapUp (c : ℤ) (θ : ℚ) : (1526 / 10 ^ 8 : ℚ) ≤ c3H17CapUp c θ := by
  rw [c3H17CapUp_eq_trCapUpper]
  exact le_trCapUpper _ _ _

/-- The grid majorant is positive: `0 < Ū_c(θ)`. -/
theorem c3H17CapUp_pos (c : ℤ) (θ : ℚ) : 0 < c3H17CapUp c θ :=
  lt_of_lt_of_le (by norm_num) (le_c3H17CapUp c θ)

/-- The grid majorant is nonnegative: `0 ≤ Ū_c(θ)`. -/
theorem c3H17CapUp_nonneg (c : ℤ) (θ : ℚ) : 0 ≤ c3H17CapUp c θ :=
  (c3H17CapUp_pos c θ).le

end CollatzPosDens
