/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr

/-!
# Towers of twos

For natural numbers `k` and `t`, the tower `tow_k(t)` is defined by `tow_0(t) = t` and
`tow_{k+1}(t) = 2 ^ tow_k(t)`; that is, `tow_k(t)` is a tower of `k` twos topped by `t`.

## Main definitions

* `CollatzPosDens.tower`: the tower `tow_k(t)`.

## Main results

* `CollatzPosDens.tower_zero`, `CollatzPosDens.tower_succ`: the defining recursion.
* `CollatzPosDens.tower_add`: `tow_{k+m}(t) = tow_k(tow_m(t))`.
* `CollatzPosDens.tower_eq_iterate`: `tow_k` is the `k`-th iterate of `t ↦ 2 ^ t`.
* `CollatzPosDens.tower_strictMono_right`: strict monotonicity in the top `t`.
* `CollatzPosDens.tower_lt_tower_succ`, `CollatzPosDens.tower_strictMono_left`,
  `CollatzPosDens.le_tower`: monotonicity in the height `k`.
* `CollatzPosDens.lt_tower_succ_of_logb_lt`: for real `y > 0`,
  `log₂ y < tow_k(t) → y < tow_{k+1}(t)`.

## Implementation notes

Mathlib's `hyperoperation 4 2 k` is a tower of `k` twos starting from `1`; the tower here starts
from an arbitrary top `t`, so it is defined directly by structural recursion on `k`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The tower of twos `tow_k(t)`: `tow_0(t) = t` and `tow_{k+1}(t) = 2 ^ tow_k(t)`. -/
@[collatz_pos_dens "def_tower"]
def tower : ℕ → ℕ → ℕ
  | 0, t => t
  | k + 1, t => 2 ^ tower k t

/-- A tower of height zero is its top: `tow_0(t) = t`. -/
@[simp]
theorem tower_zero (t : ℕ) : tower 0 t = t := rfl

/-- The recursion `tow_{k+1}(t) = 2 ^ tow_k(t)`. -/
@[simp]
theorem tower_succ (k t : ℕ) : tower (k + 1) t = 2 ^ tower k t := rfl

/-- `tow_k` is the `k`-th iterate of `t ↦ 2 ^ t`. -/
theorem tower_eq_iterate (k t : ℕ) : tower k t = (fun n : ℕ => 2 ^ n)^[k] t := by
  induction k with
  | zero => rfl
  | succ k ih => rw [tower_succ, ih, Function.iterate_succ_apply']

/-- Composition of towers: `tow_{k+m}(t) = tow_k(tow_m(t))`. -/
theorem tower_add (k m t : ℕ) : tower (k + m) t = tower k (tower m t) := by
  simp only [tower_eq_iterate, Function.iterate_add_apply]

/-- For each fixed height `k`, `t ↦ tow_k(t)` is strictly monotone. -/
theorem tower_strictMono_right (k : ℕ) : StrictMono (tower k) := by
  induction k with
  | zero => exact strictMono_id
  | succ k ih => exact fun a b h => Nat.pow_lt_pow_right Nat.one_lt_two (ih h)

/-- One more level strictly increases the tower: `tow_k(t) < tow_{k+1}(t)`. -/
theorem tower_lt_tower_succ (k t : ℕ) : tower k t < tower (k + 1) t := by
  rw [tower_succ]; exact Nat.lt_two_pow_self

/-- For each fixed top `t`, `k ↦ tow_k(t)` is strictly monotone. -/
theorem tower_strictMono_left (t : ℕ) : StrictMono (tower · t) :=
  strictMono_nat_of_lt_succ fun k => tower_lt_tower_succ k t

/-- The top is at most the tower: `t ≤ tow_k(t)`. -/
theorem le_tower (k t : ℕ) : t ≤ tower k t :=
  (tower_strictMono_left t).monotone (Nat.zero_le k)

/-- For real `y > 0`, if `log₂ y < tow_k(t)`, then `y < tow_{k+1}(t)`. -/
theorem lt_tower_succ_of_logb_lt {y : ℝ} (hy : 0 < y) {k t : ℕ}
    (h : Real.logb 2 y < (tower k t : ℝ)) : y < (tower (k + 1) t : ℝ) := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hy, Real.rpow_natCast] at h
  rw [tower_succ, Nat.cast_pow, Nat.cast_ofNat]
  exact h

end CollatzPosDens
