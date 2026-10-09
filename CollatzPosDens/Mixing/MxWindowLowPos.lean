/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxWindowLow
public import CollatzPosDens.Mixing.MxLevelNonneg

/-!
# The lower window end `q^-_n` exceeds `33n/100`

For large `n` the lower window end
$$q^-_n = \left\lfloor \tfrac12 \mathrm{Lv}_n - \tfrac14 n^{2049/4096} \right\rfloor$$
satisfies $\tfrac{33}{100} n < q^-_n$.

Since $n^{2047/4096} \ge n^{1/4} \ge 32$, we have
$\tfrac14 n^{2049/4096} = \tfrac{n}{4 n^{2047/4096}} \le \tfrac{n}{100}$, and also
$1 \le \tfrac{n}{100}$. As $\lfloor x \rfloor > x - 1$ and $\mathrm{Lv}_n \ge \tfrac{7}{10} n$,
$$q^-_n > \tfrac12 \mathrm{Lv}_n - \tfrac{n}{100} - \tfrac{n}{100}
  \ge \tfrac{7}{20} n - \tfrac{2}{100} n = \tfrac{33}{100} n.$$

## Main results

* `CollatzPosDens.mxWindowLow_pos_bound`: `33/100 · n < q^-_n` for `n ≥ 2 ^ 131072`.
* `CollatzPosDens.mxWindowLow_pos_bound_of_two_pow_eighty_le`: the same bound under the
  weaker hypothesis `n ≥ 2 ^ 80`.
* `CollatzPosDens.mxWindowLow_pos_bound_rpow_le`: `n^{2049/4096} ≤ n / 32` for `n ≥ 2 ^ 20`.

## Implementation notes

Mazur bounds $n^{2047/4096}$ below by $2^{65504}$; here the cruder bound
$n^{2047/4096} \ge n^{1/4} \ge 2^5$ is used, valid for $n \ge 2^{20}$. The argument then only
needs the level bound `seven_div_ten_mul_le_mxLevel_of_two_pow_eighty_le`, available for
$n \ge 2^{80}$; the result is specialised to $n \ge 2^{131072}$.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `n ≥ 2 ^ 20`, `n^{2049/4096} ≤ n / 32`. -/
theorem mxWindowLow_pos_bound_rpow_le {n : ℕ} (hn : 2 ^ 20 ≤ n) :
    (n : ℝ) ^ ((2049 : ℝ) / 4096) ≤ n / 32 := by
  have hnR : ((2 : ℝ) ^ 20) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ n := le_trans (by norm_num) hnR
  have h32 : (32 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have e : ((2 : ℝ) ^ 20) ^ ((1 : ℝ) / 4) = 32 := by
      rw [show ((2 : ℝ) ^ 20) = (32 : ℝ) ^ (4 : ℕ) by norm_num, one_div,
        show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.pow_rpow_inv_natCast (by norm_num)
        (by norm_num)]
    exact e ▸ Real.rpow_le_rpow (by positivity) hnR (by norm_num)
  have h14 : (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (n : ℝ) ^ ((2047 : ℝ) / 4096) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have hsplit : (n : ℝ) ^ ((2047 : ℝ) / 4096) * (n : ℝ) ^ ((2049 : ℝ) / 4096) = n := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) := by positivity
  nlinarith

/-- For every `n ≥ 2 ^ 80`, `33/100 · n < q^-_n`. -/
theorem mxWindowLow_pos_bound_of_two_pow_eighty_le {n : ℕ} (hn : 2 ^ 80 ≤ n) :
    33 / 100 * (n : ℝ) < mxWindowLow n := by
  have hrpow := mxWindowLow_pos_bound_rpow_le
    ((Nat.pow_le_pow_right (by norm_num) (by norm_num) : 2 ^ 20 ≤ 2 ^ 80).trans hn)
  have hlv := seven_div_ten_mul_le_mxLevel_of_two_pow_eighty_le hn
  have hfl := lt_mxWindowLow n
  have h100 : (100 : ℝ) ≤ n := by exact_mod_cast (show 100 ≤ n by omega)
  linarith

/-- For every integer `n ≥ 2 ^ 131072`, `33/100 · n < q^-_n`. -/
@[collatz_pos_dens "lem_mx_window_low_pos"]
theorem mxWindowLow_pos_bound {n : ℕ} (hn : 2 ^ 131072 ≤ n) :
    33 / 100 * (n : ℝ) < mxWindowLow n :=
  mxWindowLow_pos_bound_of_two_pow_eighty_le
    ((Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans hn)

end CollatzPosDens
