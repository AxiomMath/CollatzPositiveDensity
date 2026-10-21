/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Mixing.MxShKlo
public import CollatzPosDens.Mixing.MxShHLower
public import CollatzPosDens.Mixing.MxShWidthSmall

/-!
# The lower end of the shell window is positive

For every integer `n ≥ mxGateLevel = 2 ^ 80`, the lower end
`shKLo n = ⌊shHeight n / 2 - shWidth n⌋` of the shell window satisfies `1 ≤ shKLo n`.

Since `⌊u⌋ > u - 1`, the bounds `79/50 · n ≤ shHeight n` and `21600 · shWidth n ≤ n` give
$$\mathrm{shKLo}\,n > \tfrac{79}{100} n - \tfrac{n}{21600} - 1 \ge 0,$$
and an integer exceeding `0` is at least `1`.

## Main results

* `CollatzPosDens.one_le_shKLo`: for `mxGateLevel ≤ n`, `1 ≤ shKLo n`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `n ≥ mxGateLevel`, the lower end of the shell window satisfies
`1 ≤ shKLo n`. -/
@[collatz_pos_dens "lem_mx_sh_window_low"]
theorem one_le_shKLo {n : ℕ} (hn : mxGateLevel ≤ n) : 1 ≤ shKLo n := by
  rw [mxGateLevel_def] at hn
  have hH := shHeight_lower n
  have hh : (21600 * shWidth n : ℝ) ≤ n := by exact_mod_cast mul_shWidth_le hn
  have hn' : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hlt := lt_shKLo n
  have hpos : (0 : ℝ) < shKLo n := by
    have : (2 : ℝ) ≤ 2 ^ 80 := by norm_num
    linarith
  exact_mod_cast hpos

end CollatzPosDens
