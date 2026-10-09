/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Size
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Bit length

The bit length of a natural number `n` is `bl(n) := min {k ∈ ℕ : n < 2^k}`, the number of binary
digits of `n` (with `bl(0) = 0`).

## Main definitions

* `CollatzPosDens.bitLength`: the bit length `bl(n)`.

## Main results

* `CollatzPosDens.bitLength_le_iff`: `bl(n) ≤ k ↔ n < 2^k`, the characterizing property.
* `CollatzPosDens.bitLength_isLeast`: `bl(n)` is the least `k` with `n < 2^k`.
* `CollatzPosDens.bitLength_eq_sInf`: `bl(n) = sInf {k | n < 2^k}`.
* `CollatzPosDens.bitLength_spec`: `n < 2^bl(n)`.
* `CollatzPosDens.bitLength_lt_iff`: `k < bl(n) ↔ 2^k ≤ n`.
* `CollatzPosDens.bitLength_pos`: `0 < bl(n) ↔ 0 < n`.
* `CollatzPosDens.two_pow_bitLength_sub_one_le`: `2^(bl(n) - 1) ≤ n` for `0 < n`.

## Implementation notes

The bit length is Mathlib's `Nat.size`, which is characterized by `Nat.size n ≤ k ↔ n < 2^k`;
`bitLength` is an abbreviation for it, and the minimum in the definition is recovered as
`bitLength_isLeast`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The bit length `bl(n) := min {k ∈ ℕ : n < 2^k}` of a natural number, i.e. `Nat.size n`. -/
@[collatz_pos_dens "def_s02_bitlength"]
abbrev bitLength (n : ℕ) : ℕ := Nat.size n

/-- The characterizing property of the bit length: `bl(n) ≤ k ↔ n < 2^k`. -/
theorem bitLength_le_iff {n k : ℕ} : bitLength n ≤ k ↔ n < 2 ^ k := Nat.size_le

/-- Every natural number `n` satisfies `n < 2 ^ bl(n)`. -/
theorem bitLength_spec (n : ℕ) : n < 2 ^ bitLength n := Nat.lt_size_self n

/-- The bit length is the least `k` with `n < 2^k`. -/
theorem bitLength_isLeast (n : ℕ) : IsLeast {k | n < 2 ^ k} (bitLength n) :=
  ⟨bitLength_spec n, fun _ hk => bitLength_le_iff.2 hk⟩

/-- The bit length as the infimum (= minimum) of `{k | n < 2^k}`. -/
theorem bitLength_eq_sInf (n : ℕ) : bitLength n = sInf {k | n < 2 ^ k} :=
  (bitLength_isLeast n).csInf_eq.symm

/-- `k < bl(n) ↔ 2^k ≤ n`. -/
theorem bitLength_lt_iff {n k : ℕ} : k < bitLength n ↔ 2 ^ k ≤ n := Nat.lt_size

/-- For every positive natural number `n`, `2 ^ (bl(n) - 1) ≤ n`. -/
@[collatz_pos_dens "lem_s02_bl_lower"]
theorem two_pow_bitLength_sub_one_le {n : ℕ} (hn : 0 < n) : 2 ^ (bitLength n - 1) ≤ n :=
  bitLength_lt_iff.1 (Nat.sub_one_lt_of_lt (Nat.size_pos.2 hn))

/-- The bit length of `0` is `0`. -/
@[simp]
theorem bitLength_zero : bitLength 0 = 0 := Nat.size_zero

/-- The bit length of `n` is positive if and only if `n` is positive. -/
theorem bitLength_pos {n : ℕ} : 0 < bitLength n ↔ 0 < n := Nat.size_pos

end CollatzPosDens
