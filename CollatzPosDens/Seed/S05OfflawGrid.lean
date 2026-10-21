/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# The offset grid

The *offset grid* `(ξ_k)_{0 ≤ k ≤ 6198}` is a finite increasing sequence of rationals. It is
linear with step `1/512` on `[0, 8]`, `ξ_k = k/512` for `k ≤ 4096`, and geometric with ratio
`65/64` beyond, rounded to the nearest multiple of `1/512`:
$$\xi_{4096+m} = \frac{\lfloor 4096\,(65/64)^m + \tfrac12 \rfloor}{512}, \qquad 1 \le m \le 2102.$$
Every grid point is a nonnegative multiple of `1/512`, and the grid is strictly increasing.

## Main definitions

* `CollatzPosDens.offlawGrid k`: the grid point `ξ_k ∈ ℚ`.
* `CollatzPosDens.offlawGridNum k`: the natural number `512 ξ_k`, written with natural-number
  arithmetic only.

## Main results

* `CollatzPosDens.offlawGrid_eq_offlawGridNum`: `ξ_k = offlawGridNum k / 512`.
* `CollatzPosDens.offlawGrid_of_le`: `ξ_k = k / 512` for `k ≤ 4096`.
* `CollatzPosDens.offlawGrid_strictMono`: the grid is strictly increasing.
* `CollatzPosDens.offlawGrid_nonneg`, `CollatzPosDens.offlawGrid_zero`,
  `CollatzPosDens.offlawGrid_384`: `0 ≤ ξ_k`, `ξ_0 = 0`, `ξ_384 = 3/4`.
* `CollatzPosDens.offlawGridNum_6198`: the numerator of the last grid point `ξ_6198`.

## Implementation notes

The grid is indexed by all of `ℕ`: the defining formula makes sense for every `k`, and the
range `k ≤ 6198` is a hypothesis of the statements that use the grid, not of the definition.

For the kernel, `offlawGridNum` evaluates `512 ξ_{4096+m}` as the natural-number quotient
`(8192 · 65^m + 64^m) / (2 · 64^m)`, which equals `⌊4096 (65/64)^m + 1/2⌋`. This uses only
`Nat` addition, multiplication, power and division, all of which the kernel evaluates on
binary literals, so a grid point is computed by a bounded number of big-number operations
with no recursion over the index; no table of the grid is stored.

## References

* [Mazur, *Collatz positive density*], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Offset grid** `ξ_k ∈ ℚ`: `ξ_k = k/512` for `k ≤ 4096`, and
`ξ_{4096+m} = ⌊4096 (65/64)^m + 1/2⌋ / 512` for `m ≥ 1`. -/
@[collatz_pos_dens "def_s05_offlaw_grid"]
def offlawGrid (k : ℕ) : ℚ :=
  if k ≤ 4096 then (k : ℚ) / 512
  else (⌊(4096 : ℚ) * (65 / 64) ^ (k - 4096) + 1 / 2⌋ : ℚ) / 512

/-- The numerator `512 ξ_k ∈ ℕ` of the offset grid, in natural-number arithmetic:
`k` for `k ≤ 4096`, and `(8192 · 65^m + 64^m) / (2 · 64^m)` for `k = 4096 + m`. -/
def offlawGridNum (k : ℕ) : ℕ :=
  if k ≤ 4096 then k
  else (8192 * 65 ^ (k - 4096) + 64 ^ (k - 4096)) / (2 * 64 ^ (k - 4096))

/-- `⌊4096 (65/64)^m + 1/2⌋ = (8192 · 65^m + 64^m) / (2 · 64^m)`. -/
theorem floor_four_thousand_ninety_six_mul_add_half (m : ℕ) :
    ⌊(4096 : ℚ) * (65 / 64) ^ m + 1 / 2⌋ =
      (((8192 * 65 ^ m + 64 ^ m) / (2 * 64 ^ m) : ℕ) : ℤ) := by
  have h64 : (64 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have : (4096 : ℚ) * (65 / 64) ^ m + 1 / 2 =
      ((8192 * 65 ^ m + 64 ^ m : ℕ) : ℚ) / ((2 * 64 ^ m : ℕ) : ℚ) := by
    push_cast
    rw [div_pow]
    field_simp
    ring
  rw [this, Rat.floor_natCast_div_natCast, Int.natCast_div]

/-- The offset grid is `offlawGridNum k / 512`. -/
theorem offlawGrid_eq_offlawGridNum (k : ℕ) : offlawGrid k = (offlawGridNum k : ℚ) / 512 := by
  unfold offlawGrid offlawGridNum
  split_ifs
  · rfl
  · rw [floor_four_thousand_ninety_six_mul_add_half]
    rfl

/-- On the linear part, `ξ_k = k / 512`. -/
theorem offlawGrid_of_le {k : ℕ} (hk : k ≤ 4096) : offlawGrid k = (k : ℚ) / 512 := by
  simp [offlawGrid, hk]

/-- On the geometric part, `ξ_{4096+m} = ⌊4096 (65/64)^m + 1/2⌋ / 512` (also for `m = 0`). -/
theorem offlawGrid_add (m : ℕ) :
    offlawGrid (4096 + m) = (⌊(4096 : ℚ) * (65 / 64) ^ m + 1 / 2⌋ : ℚ) / 512 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [offlawGrid_of_le le_rfl]
    norm_num
  · simp [offlawGrid, show ¬ 4096 + m ≤ 4096 by omega]

/-- `ξ_0 = 0`. -/
@[simp] theorem offlawGrid_zero : offlawGrid 0 = 0 := by
  simp [offlawGrid]

/-- `ξ_384 = 3/4`. -/
theorem offlawGrid_384 : offlawGrid 384 = 3 / 4 := by
  rw [offlawGrid_of_le (by norm_num)]
  norm_num

/-- Every grid point is nonnegative. -/
theorem offlawGrid_nonneg (k : ℕ) : 0 ≤ offlawGrid k := by
  rw [offlawGrid_eq_offlawGridNum]
  positivity

/-- The numerator of the last grid point: `512 ξ_6198 = 583351470707564294`. -/
theorem offlawGridNum_6198 : offlawGridNum 6198 = 583351470707564294 := by
  decide +kernel

/-- One step of the geometric part increases the grid by at least `1/8`. -/
private theorem offlawGrid_add_succ (m : ℕ) :
    offlawGrid (4096 + m) + 1 / 8 ≤ offlawGrid (4096 + (m + 1)) := by
  rw [offlawGrid_add, offlawGrid_add]
  set x : ℚ := 4096 * (65 / 64) ^ m
  have hx : 4096 ≤ x := le_mul_of_one_le_right (by norm_num) (one_le_pow₀ (by norm_num))
  have hstep : x + 64 + 1 / 2 ≤ 4096 * (65 / 64) ^ (m + 1) + 1 / 2 := by
    rw [pow_succ, ← mul_assoc]
    change x + 64 + 1 / 2 ≤ x * (65 / 64) + 1 / 2
    linarith
  have hfl : ⌊x + 1 / 2⌋ + 64 ≤ ⌊(4096 : ℚ) * (65 / 64) ^ (m + 1) + 1 / 2⌋ := by
    calc ⌊x + 1 / 2⌋ + 64 = ⌊x + 1 / 2 + 64⌋ := (Int.floor_add_intCast _ 64).symm
      _ ≤ _ := Int.floor_mono (by linarith)
  have : ((⌊x + 1 / 2⌋ : ℤ) : ℚ) + 64 ≤
      ((⌊(4096 : ℚ) * (65 / 64) ^ (m + 1) + 1 / 2⌋ : ℤ) : ℚ) := by exact_mod_cast hfl
  linarith

/-- The offset grid is strictly increasing. -/
theorem offlawGrid_strictMono : StrictMono offlawGrid := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rcases lt_or_ge k 4096 with hk | hk
  · rw [offlawGrid_of_le hk.le, offlawGrid_of_le (by omega)]
    push_cast
    linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have := offlawGrid_add_succ m
    rw [show 4096 + m + 1 = 4096 + (m + 1) by omega]
    linarith

/-- The grid is monotone. -/
theorem offlawGrid_monotone : Monotone offlawGrid :=
  offlawGrid_strictMono.monotone

/-- The numerators of the grid are strictly increasing. -/
theorem offlawGridNum_strictMono : StrictMono offlawGridNum := fun a b hab => by
  have := offlawGrid_strictMono hab
  rw [offlawGrid_eq_offlawGridNum, offlawGrid_eq_offlawGridNum] at this
  exact_mod_cast (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 512)).1 this

end CollatzPosDens
