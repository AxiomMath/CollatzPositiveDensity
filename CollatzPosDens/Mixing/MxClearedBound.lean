/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxHeadWindow

/-!
# The cleared offset bound

For `k l : ℕ` and a word `h ∈ mxHeadGate n k l`, the offset cleared of its denominator `2^l` is
below `3^n`:
$$2^l \,\mathrm{off}(h) < 3^n.$$
Indeed, `off_le_of_mem_mxHeadGate` gives
`2^l off(h) ≤ 2^l n^{4609/4096} = 2^{l + (4609/4096) log₂ n}`, and by `mxHeadGate_add_logb_lt`
the exponent is less than `n log₂ 3`, so `2^l off(h) < 2^{n log₂ 3} = 3^n`.

## Main results

* `CollatzPosDens.two_pow_mul_off_lt_three_pow_of_mem_mxHeadGate`:
  `2^l off(h) < 3^n` for `h ∈ mxHeadGate n k l`.

## Implementation notes

The bound holds for every natural number `n`, with no hypothesis `1 ≤ n`: at `n = 0` the offset
bound reads `off(h) ≤ 0^{4609/4096} = 0`, so `2^l off(h) ≤ 0 < 1 = 3^0`. The inequality is
stated in `ℚ`, where the offset lives.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `h ∈ mxHeadGate n k l`, the cleared offset satisfies `2^l off(h) < 3^n`. -/
@[collatz_pos_dens "lem_mx_cleared_bound"]
theorem two_pow_mul_off_lt_three_pow_of_mem_mxHeadGate {n k l : ℕ} {h : Word}
    (hh : h ∈ mxHeadGate n k l) : (2 : ℚ) ^ l * off h < 3 ^ n := by
  have hoff := off_le_of_mem_mxHeadGate hh
  suffices H : (2 : ℝ) ^ l * ((off h : ℚ) : ℝ) < 3 ^ n by exact_mod_cast H
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : ((off h : ℚ) : ℝ) ≤ 0 := by
      simpa [Real.zero_rpow (by norm_num : (4609 : ℝ) / 4096 ≠ 0)] using hoff
    have h2 : (0 : ℝ) < 2 ^ l := by positivity
    simp only [pow_zero]
    nlinarith
  have e1 : (n : ℝ) ^ ((4609 : ℝ) / 4096) = (2 : ℝ) ^ (4609 / 4096 * Real.logb 2 n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hn)]
  calc (2 : ℝ) ^ l * ((off h : ℚ) : ℝ) ≤ (2 : ℝ) ^ l * (n : ℝ) ^ ((4609 : ℝ) / 4096) :=
        mul_le_mul_of_nonneg_left hoff (by positivity)
    _ = (2 : ℝ) ^ ((l : ℝ) + 4609 / 4096 * Real.logb 2 n) := by
        rw [e1, ← Real.rpow_natCast 2 l, Real.rpow_add (by norm_num)]
    _ < (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 3) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (mxHeadGate_add_logb_lt hh)
    _ = 3 ^ n := by
        rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
          (by norm_num), Real.rpow_natCast]

end CollatzPosDens
