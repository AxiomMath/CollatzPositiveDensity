/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.Recipe.NstarGate

/-!
# The scales double every `70` generations

For every $n \in \mathbb{N}$,
$$b_n \ge 16544 \cdot 2^{\lfloor n/70 \rfloor}.$$
Since $\delta = \log_2 \mathsf g > 1/70$ with $\mathsf g = 101/100$, one has
$\mathsf g^{70} = 2^{70\delta} > 2$. With $k = \lfloor n/70 \rfloor$, so $70k \le n$, and
$\mathsf g \ge 1$, this gives $\mathsf g^n \ge (\mathsf g^{70})^k \ge 2^k$, and geometric growth
of the scales gives $b_n \ge \mathsf g^n b_0 = 16544\,\mathsf g^n$.

## Main results

* `CollatzPosDens.sixteen544_mul_two_pow_div_seventy_le_scale`:
  `16544 · 2^{⌊n/70⌋} ≤ b_n`.

## Implementation notes

The statement is in `ℕ`, where both sides live; the proof passes through `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The scales double every `70` generations: for every `n ∈ ℕ`,
`16544 · 2^{⌊n/70⌋} ≤ b_n`. -/
@[collatz_pos_dens "lem_ck_scale_doubling"]
theorem sixteen544_mul_two_pow_div_seventy_le_scale (n : ℕ) :
    16544 * 2 ^ (n / 70) ≤ scale n := by
  have hg : (1 : ℝ) ≤ growthRatio := one_lt_growthRatio_cast.le
  have hpow : (2 : ℝ) ^ (n / 70) ≤ (growthRatio : ℝ) ^ n :=
    calc (2 : ℝ) ^ (n / 70) ≤ ((growthRatio : ℝ) ^ 70) ^ (n / 70) :=
          pow_le_pow_left₀ (by norm_num) two_lt_growthRatio_pow_seventy.le _
      _ = (growthRatio : ℝ) ^ (70 * (n / 70)) := by rw [← pow_mul]
      _ ≤ (growthRatio : ℝ) ^ n := pow_le_pow_right₀ hg (Nat.mul_div_le n 70)
  have h := scale_add_ge_growthRatio_pow_mul 0 n
  rw [zero_add, scale_zero] at h
  push_cast at h
  have : ((16544 * 2 ^ (n / 70) : ℕ) : ℝ) ≤ scale n := by
    push_cast
    nlinarith
  exact_mod_cast this

end CollatzPosDens
