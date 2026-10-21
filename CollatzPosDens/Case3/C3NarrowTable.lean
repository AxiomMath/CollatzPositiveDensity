/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Rat

/-!
# The narrow packet envelope table

The narrow packet envelope table is a finite table of rationals `U'_{s,t}` indexed by a set
`T' ⊆ ℤ²` of `21` pairs `(s,t)`: the pairs with `1 ≤ s ≤ 6` and `2 ≤ t ≤ 4`, together with
`(6,5)`, `(7,6)` and `(8,7)`. The entry `U'_{1,2}` is `2⁻¹⁶`; every other entry is an exact
six-digit terminating decimal. These values bound the normalized exponential sums
`t⁻¹ |∑_{m<t} exp(2πi (2^m - 1)(b + β)/2^s)|` near odd dyadic angles.

## Main definitions

* `CollatzPosDens.c3NarrowTableDomain`: the index set `T'` as a `Finset (ℤ × ℤ)`.
* `CollatzPosDens.c3NarrowTable s t`: the table entry `U'_{s,t}` (and `0` off `T'`).

## Main results

* `CollatzPosDens.card_c3NarrowTableDomain`: `T'` has `21` elements.
* `CollatzPosDens.mem_c3NarrowTableDomain_bounds`: every `(s,t) ∈ T'` has `1 ≤ s ≤ 8` and
  `2 ≤ t ≤ 7`.
* `CollatzPosDens.c3NarrowTable_eq_zero_of_not_mem`: the entry is `0` off `T'`.
* `CollatzPosDens.c3NarrowTable_pos`: on `T'`, `0 < U'_{s,t}`.
* `CollatzPosDens.c3NarrowTable_nonneg`, `CollatzPosDens.c3NarrowTable_lt_one`: everywhere,
  `0 ≤ U'_{s,t} < 1`.

## Implementation notes

The function `U' : T' → ℚ` is represented by a total function `ℤ → ℤ → ℚ` together
with the finite set `T'`; consumers hypothesize `(s,t) ∈ c3NarrowTableDomain`. Off `T'` the
function takes the junk value `0`. Indices are integers, so that a consumer may index the table
at a difference `o - i` without truncation.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The index set `T'` of the narrow packet envelope table: the pairs `(s,t)` with
`1 ≤ s ≤ 6` and `2 ≤ t ≤ 4`, together with `(6,5)`, `(7,6)` and `(8,7)`; `21` pairs in all. -/
@[collatz_pos_dens "def_c3_narrow_table"]
def c3NarrowTableDomain : Finset (ℤ × ℤ) :=
  {(1, 2), (1, 3), (1, 4),
   (2, 2), (2, 3), (2, 4),
   (3, 2), (3, 3), (3, 4),
   (4, 2), (4, 3), (4, 4),
   (5, 2), (5, 3), (5, 4),
   (6, 2), (6, 3), (6, 4), (6, 5),
   (7, 6),
   (8, 7)}

/-- The narrow packet envelope table `U'_{s,t}` on `T' = c3NarrowTableDomain`: `U'_{1,2} = 2⁻¹⁶`
and the other entries are exact six-digit decimals; the junk value off `T'` is `0`. -/
@[collatz_pos_dens "def_c3_narrow_table"]
def c3NarrowTable : ℤ → ℤ → ℚ
  | 1, 2 => 1 / 2 ^ 16
  | 1, 3 => 333340 / 1000000
  | 1, 4 => 500010 / 1000000
  | 2, 2 => 707108 / 1000000
  | 2, 3 => 333337 / 1000000
  | 2, 4 => 353560 / 1000000
  | 3, 2 => 923880 / 1000000
  | 3, 3 => 577352 / 1000000
  | 3, 4 => 461943 / 1000000
  | 4, 2 => 980786 / 1000000
  | 4, 3 => 883638 / 1000000
  | 4, 4 => 604555 / 1000000
  | 5, 2 => 995185 / 1000000
  | 5, 3 => 970239 / 1000000
  | 5, 4 => 867542 / 1000000
  | 6, 2 => 998796 / 1000000
  | 6, 3 => 992518 / 1000000
  | 6, 4 => 965743 / 1000000
  | 6, 5 => 864601 / 1000000
  | 7, 6 => 868067 / 1000000
  | 8, 7 => 874299 / 1000000
  | _, _ => 0

/-- The index set `T'` has `21` elements. -/
theorem card_c3NarrowTableDomain : c3NarrowTableDomain.card = 21 := by decide

/-- Every pair of `T'` has `1 ≤ s ≤ 8` and `2 ≤ t ≤ 7`. -/
theorem mem_c3NarrowTableDomain_bounds {s t : ℤ} (h : (s, t) ∈ c3NarrowTableDomain) :
    1 ≤ s ∧ s ≤ 8 ∧ 2 ≤ t ∧ t ≤ 7 := by
  simp only [c3NarrowTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  omega

/-- Off `T'` the table takes the junk value `0`. -/
theorem c3NarrowTable_eq_zero_of_not_mem {s t : ℤ} (h : (s, t) ∉ c3NarrowTableDomain) :
    c3NarrowTable s t = 0 := by
  simp only [c3NarrowTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    not_or, not_and] at h
  unfold c3NarrowTable
  split <;> simp_all

/-- Every entry of the table on `T'` is positive. -/
theorem c3NarrowTable_pos {s t : ℤ} (h : (s, t) ∈ c3NarrowTableDomain) :
    0 < c3NarrowTable s t := by
  simp only [c3NarrowTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> norm_num [c3NarrowTable]

/-- Every entry of the table is less than `1`. -/
theorem c3NarrowTable_lt_one (s t : ℤ) : c3NarrowTable s t < 1 := by
  unfold c3NarrowTable
  split <;> norm_num

/-- Every entry of the table is nonnegative. -/
theorem c3NarrowTable_nonneg (s t : ℤ) : 0 ≤ c3NarrowTable s t := by
  unfold c3NarrowTable
  split <;> norm_num

end CollatzPosDens
