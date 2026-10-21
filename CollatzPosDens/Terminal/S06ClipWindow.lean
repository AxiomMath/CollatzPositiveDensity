/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Order.Group.Int
public import CollatzPosDens.Terminal.S06ClipWidth
public import CollatzPosDens.Terminal.S06ClipFloor

/-!
# The clipping degree window

For integers `m ≥ 1`, `n ≥ 2` and a real `B > 0`, the *clipping degree window* is the set of
integers
$$I^{\mathrm{clp}}_{m,n,B} = \{A \in ℤ : 2m - w^{\mathrm{clp}}_{m,n} ≤ A
  ≤ 2m + w^{\mathrm{clp}}_{m,n} \text{ and } A ≥ \max(m, A^{\mathrm{clp}}_{m,B})\},$$
the central window of half-width `w^clp_{m,n}` around `2m`, cut below at `m` and at the clipping
degree floor `A^clp_{m,B}`.

## Main definitions

* `CollatzPosDens.clipWindow m n B`: the window `I^clp_{m,n,B}`, as a finite set of integers.

## Main results

* `CollatzPosDens.mem_clipWindow`: membership in `I^clp_{m,n,B}` is the defining condition.
* `CollatzPosDens.card_clipWindow_le`: `#I^clp_{m,n,B} ≤ 2 w^clp_{m,n} + 1`.

## Implementation notes

The window is a bounded set of integers, so it is a `Finset ℤ`: the interval
`[2m - w, 2m + w]` filtered by `max(m, A^clp_{m,B}) ≤ A`. The definition makes sense for all
`m, n ∈ ℕ` and `B ∈ ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping degree window: the integers `A` with `2m - w ≤ A ≤ 2m + w` and
`max(m, A^clp_{m,B}) ≤ A`, where `w = w^clp_{m,n}`. -/
@[collatz_pos_dens "def_s06_clip_window"]
noncomputable def clipWindow (m n : ℕ) (B : ℝ) : Finset ℤ :=
  (Finset.Icc (2 * m - clipWidth m n : ℤ) (2 * m + clipWidth m n)).filter
    fun A => max (m : ℤ) (clipFloor m B) ≤ A

/-- Membership in the clipping degree window. -/
@[simp]
theorem mem_clipWindow {m n : ℕ} {B : ℝ} {A : ℤ} :
    A ∈ clipWindow m n B ↔
      (2 * m - clipWidth m n : ℤ) ≤ A ∧ A ≤ 2 * m + clipWidth m n ∧
        max (m : ℤ) (clipFloor m B) ≤ A := by
  simp [clipWindow, and_assoc]

/-- The clipping degree window has at most `2 w^clp_{m,n} + 1` elements. -/
theorem card_clipWindow_le (m n : ℕ) (B : ℝ) :
    (clipWindow m n B).card ≤ 2 * clipWidth m n + 1 := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Int.card_Icc]
  omega

/-- Every element of the clipping degree window is at least `m`. -/
theorem le_of_mem_clipWindow {m n : ℕ} {B : ℝ} {A : ℤ} (h : A ∈ clipWindow m n B) :
    (m : ℤ) ≤ A :=
  (le_max_left _ _).trans (mem_clipWindow.1 h).2.2

/-- Every element of the clipping degree window is at least the clipping floor. -/
theorem clipFloor_le_of_mem_clipWindow {m n : ℕ} {B : ℝ} {A : ℤ} (h : A ∈ clipWindow m n B) :
    clipFloor m B ≤ A :=
  (le_max_right _ _).trans (mem_clipWindow.1 h).2.2

end CollatzPosDens
