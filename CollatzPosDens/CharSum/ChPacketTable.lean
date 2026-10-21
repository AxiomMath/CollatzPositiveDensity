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
# The packet envelope table

The packet envelope table is a finite table of exact terminating decimals `U_{s,t}` indexed by
a set `T_U ⊆ ℤ_{≥1} × ℤ_{≥2}` of `21` pairs `(s,t)`: for `1 ≤ s ≤ 6` the columns `t = 2, 3, 4`,
together with `(6,5)`, `(7,6)` and `(8,7)`.

## Main definitions

* `CollatzPosDens.chPacketTableDomain`: the index set `T_U` as a `Finset (ℕ × ℕ)`.
* `CollatzPosDens.chPacketTable s t`: the table entry `U_{s,t}` (and `0` off `T_U`).

## Main results

* `CollatzPosDens.card_chPacketTableDomain`: `T_U` has `21` elements.
* `CollatzPosDens.mem_chPacketTableDomain_bounds`: every `(s,t) ∈ T_U` has `1 ≤ s` and `2 ≤ t`.
* `CollatzPosDens.chPacketTable_eq_zero_of_not_mem`: the entry is `0` off `T_U`.
* `CollatzPosDens.chPacketTable_pos`, `CollatzPosDens.chPacketTable_le_one`: on `T_U`,
  `0 < U_{s,t} ≤ 1`.

## Implementation notes

The table `U : T_U → ℚ` is represented by a total function `ℕ → ℕ → ℚ` together with the
finite set `T_U`; consumers hypothesize `(s,t) ∈ chPacketTableDomain`. Off `T_U` the
function takes the junk value `0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The index set `T_U` of the packet envelope table: the `21` pairs `(s,t)` with
`1 ≤ s ≤ 6, t ∈ {2,3,4}`, together with `(6,5)`, `(7,6)` and `(8,7)`. -/
@[collatz_pos_dens "def_ch_packet_table"]
def chPacketTableDomain : Finset (ℕ × ℕ) :=
  {(1, 2), (1, 3), (1, 4),
   (2, 2), (2, 3), (2, 4),
   (3, 2), (3, 3), (3, 4),
   (4, 2), (4, 3), (4, 4),
   (5, 2), (5, 3), (5, 4),
   (6, 2), (6, 3), (6, 4), (6, 5),
   (7, 6),
   (8, 7)}

/-- The packet envelope table `U_{s,t}` on `T_U = chPacketTableDomain`, given by exact
terminating decimals; the junk value off `T_U` is `0`. -/
@[collatz_pos_dens "def_ch_packet_table"]
def chPacketTable : ℕ → ℕ → ℚ
  | 1, 2 => 1 / 2
  | 1, 3 => 590 / 1000
  | 1, 4 => 504 / 1000
  | 2, 2 => 867 / 1000
  | 2, 3 => 579 / 1000
  | 2, 4 => 626 / 1000
  | 3, 2 => 96593 / 100000
  | 3, 3 => 800 / 1000
  | 3, 4 => 535 / 1000
  | 4, 2 => 992 / 1000
  | 4, 3 => 94741 / 100000
  | 4, 4 => 775 / 1000
  | 5, 2 => 99786 / 100000
  | 5, 3 => 98672 / 100000
  | 5, 4 => 93963 / 100000
  | 6, 2 => 999465 / 1000000
  | 6, 3 => 996672 / 1000000
  | 6, 4 => 984682 / 1000000
  | 6, 5 => 939 / 1000
  | 7, 6 => 940 / 1000
  | 8, 7 => 943 / 1000
  | _, _ => 0

/-- The index set `T_U` has `21` elements. -/
theorem card_chPacketTableDomain : chPacketTableDomain.card = 21 := by decide

/-- Every pair of `T_U` lies in `ℤ_{≥1} × ℤ_{≥2}`. -/
theorem mem_chPacketTableDomain_bounds {s t : ℕ} (h : (s, t) ∈ chPacketTableDomain) :
    1 ≤ s ∧ 2 ≤ t := by
  simp only [chPacketTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  omega

/-- Off `T_U` the table takes the junk value `0`. -/
theorem chPacketTable_eq_zero_of_not_mem {s t : ℕ} (h : (s, t) ∉ chPacketTableDomain) :
    chPacketTable s t = 0 := by
  simp only [chPacketTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    not_or, not_and] at h
  unfold chPacketTable
  split <;> simp_all

/-- Every entry of the table on `T_U` is positive. -/
theorem chPacketTable_pos {s t : ℕ} (h : (s, t) ∈ chPacketTableDomain) :
    0 < chPacketTable s t := by
  simp only [chPacketTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> norm_num [chPacketTable]

/-- Every entry of the table is at most `1`. -/
theorem chPacketTable_le_one (s t : ℕ) : chPacketTable s t ≤ 1 := by
  unfold chPacketTable
  split <;> norm_num

end CollatzPosDens
