/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Mixing.MxShKhi
public import CollatzPosDens.Mixing.MxShHUpper
public import CollatzPosDens.Mixing.MxShWidthSmall

/-!
# A linear bound on the upper end of the shell window

For every integer `n ≥ mxGateLevel = 2 ^ 80`, the upper end
`shKHi n = ⌈shHeight n / 2 + shWidth n⌉` of the shell window satisfies
$$21600 \cdot \mathrm{shKHi}(n) < 17119\, n + 32400.$$

## Main results

* `CollatzPosDens.mul_shKHi_lt`: for `mxGateLevel ≤ n`, `21600 * shKHi n < 17119 * n + 32400`.

## References

* [Mazur, *Collatz positive density*]
-/
@[expose] public section

namespace CollatzPosDens

/-- For every integer `n ≥ n₀`, the upper end of the shell window satisfies
`21600 k^{sh,+}_n < 17119 n + 32400`. -/
@[collatz_pos_dens "lem_mx_sh_window_high"]
theorem mul_shKHi_lt {n : ℕ} (hn : mxGateLevel ≤ n) :
    21600 * shKHi n < 17119 * (n : ℤ) + 32400 := by
  rw [mxGateLevel_def] at hn
  have hk := shKHi_lt n
  have hH := shHeight_lt_linear n
  have hw : (21600 * shWidth n : ℝ) ≤ n := by exact_mod_cast mul_shWidth_le hn
  have : (21600 * shKHi n : ℝ) < 17119 * (n : ℝ) + 32400 := by linarith
  exact_mod_cast this

end CollatzPosDens
