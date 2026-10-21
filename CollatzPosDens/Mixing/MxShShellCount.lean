/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Mixing.MxShJ
public import CollatzPosDens.Mixing.MxShLogLower

/-!
# A bound on the number of offset shells

For every integer $n \ge n_0$, where $n_0 = 2^{80}$ is the mixing gate level
`CollatzPosDens.mxGateLevel`, the number of offset shells of the shell cut satisfies
$J^{\mathrm{sh}}_n + 1 < 3 \log n$.

Put $L = \log n$. Since $\log 2 > 0.693$, we have $2 \log_2 n = 2L / \log 2 < \frac{2000}{693} L$,
so $J^{\mathrm{sh}}_n + 1 < 2 \log_2 n + 2 < \frac{2000}{693} L + 2$. Since $L \ge \frac{160}{3}$,
we have $2 \le \frac{3}{80} L$, and $\frac{2000}{693} + \frac{3}{80} < 3$.

## Main results

* `CollatzPosDens.shJ_add_one_lt_three_mul_log`: for `n₀ ≤ n`, `J^sh_n + 1 < 3 log n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `n ≥ n₀`, the number of offset shells satisfies `J^sh_n + 1 < 3 log n`.
-/
@[collatz_pos_dens "lem_mx_sh_shell_count"]
theorem shJ_add_one_lt_three_mul_log {n : ℕ} (hn : mxGateLevel ≤ n) :
    (shJ n : ℝ) + 1 < 3 * Real.log n := by
  rw [mxGateLevel_def] at hn
  have hL : (160 / 3 : ℝ) ≤ Real.log n :=
    le_log_of_two_pow_eighty_le (by exact_mod_cast hn)
  have hlog2 := log_two_bounds.1
  have hJ := shJ_lt_add_one n
  have hb : 2 * Real.logb 2 n ≤ 2000 / 693 * Real.log n := by
    rw [Real.logb, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  linarith

end CollatzPosDens
