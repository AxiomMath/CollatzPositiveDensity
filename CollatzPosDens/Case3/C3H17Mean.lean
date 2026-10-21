/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Table

/-!
# Orbit means of the height-seventeen cost table

For integers `c, o` with `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and `s ∈ {1, 3, 5, 7}`, the orbit mean
`μʰ_{c,o,s}` is the average of the cost table `ct_{c,o}` over the first `2^14` points of the orbit
of `s` under multiplication by `9`:
`μʰ_{c,o,s} = 2^{-14} ∑_{k=0}^{2^14-1} ct_{c,o}(9^k s)`.
Since `9^{2^14} ≡ 1 (mod 2^17)` and the table depends on its argument modulo `2^17`, this is the
mean of `ct_{c,o}` along a full period of the orbit.

## Main definitions

* `CollatzPosDens.c3H17Mean`: the orbit mean `μʰ_{c,o,s}`.

## Main results

* `CollatzPosDens.c3H17Mean_mul`: `2^14 μʰ_{c,o,s}` is the orbit sum.
* `CollatzPosDens.c3H17Mean_le_one`: the orbit mean is at most `1`.

## Implementation notes

The indices `c, o, s` range over all of `ℤ`, and the same formula is used outside the range
`2 ≤ c ≤ 16`, `1 ≤ o ≤ c`, `s ∈ {1, 3, 5, 7}`, where the mean is not otherwise defined.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The orbit mean `μʰ_{c,o,s} = 2^{-14} ∑_{k=0}^{2^14-1} ct_{c,o}(9^k s)` of the
height-seventeen cost table. -/
@[collatz_pos_dens "def_c3_h17_mean"]
def c3H17Mean (c o s : ℤ) : ℚ :=
  (∑ k ∈ range (2 ^ 14), c3H17Table c o (9 ^ k * s)) / 2 ^ 14

/-- `2^14` times the orbit mean is the orbit sum of the cost table. -/
theorem c3H17Mean_mul (c o s : ℤ) :
    2 ^ 14 * c3H17Mean c o s = ∑ k ∈ range (2 ^ 14), c3H17Table c o (9 ^ k * s) := by
  unfold c3H17Mean
  field_simp

/-- The orbit mean is at most `1`, since every table entry is. -/
theorem c3H17Mean_le_one (c o s : ℤ) : c3H17Mean c o s ≤ 1 := by
  unfold c3H17Mean
  rw [div_le_one (by positivity)]
  calc ∑ k ∈ range (2 ^ 14), c3H17Table c o (9 ^ k * s)
      ≤ ∑ _k ∈ range (2 ^ 14), (1 : ℚ) := sum_le_sum fun k _ => c3H17Table_le_one _ _ _
    _ = 2 ^ 14 := by norm_num

end CollatzPosDens
