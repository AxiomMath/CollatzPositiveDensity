/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.OrdinaryTime.CkScaleDoubling
public import CollatzPosDens.Recipe.CovGen

/-!
# Late growth of the scales

The scales `b_n` dominate `2^{40} n` from the coverage generation on: for every integer
`n ≥ J_c = 23000`,
$$b_n \ge 2^{40} n.$$
Put `k = ⌊n/70⌋`, so `k ≥ ⌊23000/70⌋ = 328` and `n < 70(k + 1)`. By induction on `k ≥ 328`,
`2^{k-26} ≥ 70(k + 1)`: the base case is `2^{302} ≥ 23030`, and doubling the left side more than
covers the step `70(k+1) ↦ 70(k+2)`. The scales double every `70` generations and
`16544 ≥ 2^{14}`, so
$$b_n \ge 16544 \cdot 2^k \ge 2^{14+k} = 2^{40} \cdot 2^{k-26} \ge 2^{40} \cdot 70(k+1)
  > 2^{40} n.$$

## Main results

* `CollatzPosDens.two_pow_forty_mul_le_scale`: `2^{40} n ≤ b_n` for `n ≥ J_c`.

## Implementation notes

The statement is in `ℕ`, which is the strongest form, since `b_n` is a natural number. The
induction is written with `k = 328 + m`, avoiding truncated subtraction in the exponent.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `70 (329 + m) ≤ 2^{302 + m}` for every `m`, i.e. `70 (k + 1) ≤ 2^{k - 26}` for `k ≥ 328`. -/
private theorem seventy_mul_le_two_pow_add (m : ℕ) : 70 * (329 + m) ≤ 2 ^ (302 + m) := by
  induction m with
  | zero =>
    have h : 2 ^ 15 ≤ 2 ^ (302 + 0) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by norm_num : 15 ≤ 302 + 0)
    generalize 2 ^ (302 + 0) = P at h ⊢
    omega
  | succ m ih =>
    rw [← add_assoc, ← add_assoc, pow_succ]
    have : 1 ≤ 2 ^ (302 + m) := Nat.one_le_two_pow
    omega

/-- **Late scales are large**: for every integer `n ≥ J_c`, `2^{40} n ≤ b_n`. -/
@[collatz_pos_dens "lem_ck_late_growth"]
theorem two_pow_forty_mul_le_scale (n : ℕ) (hn : covGen ≤ n) :
    2 ^ 40 * n ≤ scale n := by
  rw [covGen_def] at hn
  obtain ⟨m, hm⟩ : ∃ m, n / 70 = 328 + m := ⟨n / 70 - 328, by omega⟩
  have hlt : n < 70 * (329 + m) := by omega
  have hd := sixteen544_mul_two_pow_div_seventy_le_scale n
  rw [hm] at hd
  have hk := seventy_mul_le_two_pow_add m
  calc 2 ^ 40 * n ≤ 2 ^ 40 * (70 * (329 + m)) := Nat.mul_le_mul_left _ hlt.le
    _ ≤ 2 ^ 40 * 2 ^ (302 + m) := Nat.mul_le_mul_left _ hk
    _ = 2 ^ 14 * 2 ^ (328 + m) := by
        rw [← pow_add, ← pow_add, show 40 + (302 + m) = 14 + (328 + m) by omega]
    _ ≤ 16544 * 2 ^ (328 + m) := Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ scale n := hd

end CollatzPosDens
