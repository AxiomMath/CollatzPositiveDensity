/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Mean

/-!
# Orbit ranges of the height-seventeen cost table

For integers `c, o` with `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and `s ∈ {1, 3, 5, 7}`, the centred partial sums
of the cost table along the orbit of `s` under multiplication by `9` are
`P_k = ∑_{j=0}^{k-1} (ct_{c,o}(9^j s) - μʰ_{c,o,s})`, and the orbit range is
`rg_{c,o,s} = max_{0 ≤ k ≤ 2^14} P_k - min_{0 ≤ k ≤ 2^14} P_k`, a rational number.

## Main definitions

* `CollatzPosDens.c3H17CentredSum`: the centred partial sum `P_k`.
* `CollatzPosDens.c3H17Range`: the orbit range `rg_{c,o,s}`.

## Main results

* `CollatzPosDens.c3H17CentredSum_zero`: `P_0 = 0`.
* `CollatzPosDens.c3H17CentredSum_two_pow_fourteen`: `P_{2^14} = 0`.
* `CollatzPosDens.c3H17CentredSum_sub_le_c3H17Range`: `P_k - P_l ≤ rg_{c,o,s}` for
  `k, l ≤ 2^14`.
* `CollatzPosDens.c3H17Range_nonneg`: `0 ≤ rg_{c,o,s}`.

## Implementation notes

The maximum and minimum are `Finset.sup'` and `Finset.inf'` over `Finset.range (2^14 + 1)`. The
indices `c, o, s` range over all of `ℤ`, and the same formula is used outside the range
`2 ≤ c ≤ 16`, `1 ≤ o ≤ c`, `s ∈ {1, 3, 5, 7}`, where the orbit range is not otherwise defined.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The centred partial sum `P_k = ∑_{j=0}^{k-1} (ct_{c,o}(9^j s) - μʰ_{c,o,s})` of the
height-seventeen cost table along the orbit of `s` under multiplication by `9`. -/
def c3H17CentredSum (c o s : ℤ) (k : ℕ) : ℚ :=
  ∑ j ∈ range k, (c3H17Table c o (9 ^ j * s) - c3H17Mean c o s)

/-- The orbit range
`rg_{c,o,s} = max_{0 ≤ k ≤ 2^14} P_k - min_{0 ≤ k ≤ 2^14} P_k` of the centred partial sums
`P_k = ∑_{j=0}^{k-1} (ct_{c,o}(9^j s) - μʰ_{c,o,s})`. -/
@[collatz_pos_dens "def_c3_h17_range"]
def c3H17Range (c o s : ℤ) : ℚ :=
  (range (2 ^ 14 + 1)).sup' nonempty_range_add_one (c3H17CentredSum c o s) -
    (range (2 ^ 14 + 1)).inf' nonempty_range_add_one (c3H17CentredSum c o s)

/-- The empty centred partial sum vanishes: `P_0 = 0`. -/
@[simp]
theorem c3H17CentredSum_zero (c o s : ℤ) : c3H17CentredSum c o s 0 = 0 := by
  simp [c3H17CentredSum]

/-- The recursion `P_{k+1} = P_k + (ct_{c,o}(9^k s) - μʰ_{c,o,s})` for the centred partial sums. -/
theorem c3H17CentredSum_succ (c o s : ℤ) (k : ℕ) :
    c3H17CentredSum c o s (k + 1) =
      c3H17CentredSum c o s k + (c3H17Table c o (9 ^ k * s) - c3H17Mean c o s) := by
  simp only [c3H17CentredSum, sum_range_succ]

/-- The centred partial sum over a full period vanishes: `P_{2^14} = 0`. -/
theorem c3H17CentredSum_two_pow_fourteen (c o s : ℤ) : c3H17CentredSum c o s (2 ^ 14) = 0 := by
  have h := c3H17Mean_mul c o s
  rw [c3H17CentredSum, sum_sub_distrib, ← h]
  simp only [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- Every centred partial sum with `k ≤ 2^14` is at most the maximum. -/
theorem c3H17CentredSum_le_sup' (c o s : ℤ) {k : ℕ} (hk : k ≤ 2 ^ 14) :
    c3H17CentredSum c o s k ≤
      (range (2 ^ 14 + 1)).sup' nonempty_range_add_one (c3H17CentredSum c o s) :=
  le_sup' _ (mem_range.mpr (Nat.lt_succ_of_le hk))

/-- Every centred partial sum with `k ≤ 2^14` is at least the minimum. -/
theorem inf'_le_c3H17CentredSum (c o s : ℤ) {k : ℕ} (hk : k ≤ 2 ^ 14) :
    (range (2 ^ 14 + 1)).inf' nonempty_range_add_one (c3H17CentredSum c o s) ≤
      c3H17CentredSum c o s k :=
  inf'_le _ (mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The orbit range bounds the difference of any two centred partial sums with indices at most
`2^14`. -/
theorem c3H17CentredSum_sub_le_c3H17Range (c o s : ℤ) {k l : ℕ} (hk : k ≤ 2 ^ 14)
    (hl : l ≤ 2 ^ 14) : c3H17CentredSum c o s k - c3H17CentredSum c o s l ≤ c3H17Range c o s :=
  sub_le_sub (c3H17CentredSum_le_sup' c o s hk) (inf'_le_c3H17CentredSum c o s hl)

/-- The orbit range bounds the distance between any two centred partial sums with indices at most
`2^14`. -/
theorem abs_c3H17CentredSum_sub_le_c3H17Range (c o s : ℤ) {k l : ℕ} (hk : k ≤ 2 ^ 14)
    (hl : l ≤ 2 ^ 14) : |c3H17CentredSum c o s k - c3H17CentredSum c o s l| ≤ c3H17Range c o s :=
  abs_sub_le_iff.mpr ⟨c3H17CentredSum_sub_le_c3H17Range c o s hk hl,
    c3H17CentredSum_sub_le_c3H17Range c o s hl hk⟩

/-- Every centred partial sum with `k ≤ 2^14` has absolute value at most the orbit range. -/
theorem abs_c3H17CentredSum_le_c3H17Range (c o s : ℤ) {k : ℕ} (hk : k ≤ 2 ^ 14) :
    |c3H17CentredSum c o s k| ≤ c3H17Range c o s := by
  simpa using abs_c3H17CentredSum_sub_le_c3H17Range c o s hk (Nat.zero_le _)

/-- The orbit range is nonnegative. -/
theorem c3H17Range_nonneg (c o s : ℤ) : 0 ≤ c3H17Range c o s :=
  (abs_nonneg _).trans (abs_c3H17CentredSum_le_c3H17Range c o s (k := 0) (Nat.zero_le _))

end CollatzPosDens
