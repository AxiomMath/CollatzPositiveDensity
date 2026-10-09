/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHold
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Hold-list weights

Let `𝒫 = ℤ_{≥1} × ℤ` be the set of steps `(j, l)` and `η = CollatzPosDens.holdLaw` the holding-time
law on `𝒫`. For `N ∈ ℕ` and a hold list `h = (h_1, …, h_N) ∈ 𝒫^N`, the hold-list weight is the
product `η^{⊗N}(h) = ∏_{i=1}^N η(h_i)`: the probability of drawing the steps `h_1, …, h_N`
independently from `η`.

## Main definitions

* `CollatzPosDens.holdListLaw h`: the weight `η^{⊗N}(h) = ∏_i η(h_i)` of `h : Fin N → ℕ × ℤ`.

## Main results

* `CollatzPosDens.holdListLaw_zero`: the empty hold list has weight `1`.
* `CollatzPosDens.holdListLaw_cons`, `CollatzPosDens.holdListLaw_snoc`: splitting off the
  first or the last step.
* `CollatzPosDens.holdListLaw_append`: the weight is multiplicative under concatenation.
* `CollatzPosDens.holdListLaw_nonneg`: `0 ≤ η^{⊗N}(h)`.

## Implementation notes

A point `p = (j, l)` is a pair `ℕ × ℤ`, matching the signature `holdLaw j l` of the holding-time
law, and a hold list of length `N` is a tuple `Fin N → ℕ × ℤ`. The set `𝒫` consists of the pairs
with `j ≥ 1`; the weight is defined for all tuples of pairs, which generalizes the domain `𝒫^N`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The hold-list weight `η^{⊗N}(h) = ∏_{i=1}^N η(h_i)` of a hold list `h = (h_1, …, h_N)`. -/
@[collatz_pos_dens "def_rn_hold_list"]
noncomputable def holdListLaw {N : ℕ} (h : Fin N → ℕ × ℤ) : ℝ :=
  ∏ i, holdLaw (h i).1 (h i).2

/-- The hold-list weight of `h` is the product `∏_i η(h_i)` of the holding-time law over its
entries. -/
theorem holdListLaw_def {N : ℕ} (h : Fin N → ℕ × ℤ) :
    holdListLaw h = ∏ i, holdLaw (h i).1 (h i).2 :=
  rfl

/-- The empty hold list has weight `1`. -/
@[simp]
theorem holdListLaw_zero (h : Fin 0 → ℕ × ℤ) : holdListLaw h = 1 := by
  simp [holdListLaw]

/-- Splitting off the first step. -/
@[simp]
theorem holdListLaw_cons {N : ℕ} (a : ℕ × ℤ) (h : Fin N → ℕ × ℤ) :
    holdListLaw (Fin.cons a h : Fin (N + 1) → ℕ × ℤ) = holdLaw a.1 a.2 * holdListLaw h := by
  simp [holdListLaw, Fin.prod_univ_succ]

/-- Splitting off the first step of a tuple of length `N + 1`. -/
theorem holdListLaw_succ {N : ℕ} (h : Fin (N + 1) → ℕ × ℤ) :
    holdListLaw h = holdLaw (h 0).1 (h 0).2 * holdListLaw (Fin.tail h) := by
  simp [holdListLaw, Fin.prod_univ_succ, Fin.tail]

/-- Splitting off the last step. -/
@[simp]
theorem holdListLaw_snoc {N : ℕ} (h : Fin N → ℕ × ℤ) (a : ℕ × ℤ) :
    holdListLaw (Fin.snoc h a : Fin (N + 1) → ℕ × ℤ) = holdListLaw h * holdLaw a.1 a.2 := by
  simp [holdListLaw, Fin.prod_univ_castSucc]

/-- The weight of a one-step hold list. -/
theorem holdListLaw_one (h : Fin 1 → ℕ × ℤ) : holdListLaw h = holdLaw (h 0).1 (h 0).2 := by
  simp [holdListLaw]

/-- The weight is multiplicative under concatenation. -/
@[simp]
theorem holdListLaw_append {a b : ℕ} (u : Fin a → ℕ × ℤ) (v : Fin b → ℕ × ℤ) :
    holdListLaw (Fin.append u v) = holdListLaw u * holdListLaw v := by
  simp [holdListLaw, Fin.prod_univ_add]

/-- The hold-list weight is nonnegative. -/
theorem holdListLaw_nonneg {N : ℕ} (h : Fin N → ℕ × ℤ) : 0 ≤ holdListLaw h :=
  Finset.prod_nonneg fun _ _ ↦ holdLaw_nonneg _ _

end CollatzPosDens
