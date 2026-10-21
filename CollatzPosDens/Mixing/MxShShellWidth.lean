/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShShell

/-!
# Widths of the offset shells

For `j ∈ ℕ` the width of the offset shell `I^{sh}_j` is the natural number
$$W_0 = 1, \qquad W_j = 2^{j-1} \quad (j \ge 1).$$
It is the length of `I^{sh}_j`: writing `α_0 = 0` and `α_j = 2^{j-1}` for `j ≥ 1`, the shell is
the half-open interval `I^{sh}_j = [α_j, α_j + W_j)`.

## Main definitions

* `CollatzPosDens.shShellWidth`: the width `W_j`.

## Main results

* `CollatzPosDens.shShellWidth_zero`, `CollatzPosDens.shShellWidth_succ`,
  `CollatzPosDens.shShellWidth_of_ne_zero`: the values of `W_j`.
* `CollatzPosDens.shShellWidth_pos`, `CollatzPosDens.shShellWidth_le_two_pow`:
  `1 ≤ W_j ≤ 2^j`.
* `CollatzPosDens.mxShShell_eq_Ico_shShellWidth`: `I^{sh}_j = [α_j, α_j + W_j)` for some
  `α_j ≥ 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The width `W_j` of the offset shell `I^{sh}_j`: `W_0 = 1` and `W_j = 2^{j-1}` for `j ≥ 1`. -/
@[collatz_pos_dens "def_mx_sh_width"]
def shShellWidth : ℕ → ℕ
  | 0 => 1
  | j + 1 => 2 ^ j

/-- The width of the shell `I^{sh}_0` is `W_0 = 1`. -/
@[simp]
theorem shShellWidth_zero : shShellWidth 0 = 1 := rfl

/-- For every `j`, the width of `I^{sh}_{j+1}` is `W_{j+1} = 2^j`. -/
@[simp]
theorem shShellWidth_succ (j : ℕ) : shShellWidth (j + 1) = 2 ^ j := rfl

/-- For `j ≥ 1`, `W_j = 2^{j-1}`. -/
theorem shShellWidth_of_ne_zero {j : ℕ} (hj : j ≠ 0) : shShellWidth j = 2 ^ (j - 1) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  simp

/-- Every shell width is positive. -/
theorem shShellWidth_pos (j : ℕ) : 0 < shShellWidth j := by
  cases j <;> simp

/-- The width of `I^{sh}_j` is at most `2^j`. -/
theorem shShellWidth_le_two_pow (j : ℕ) : shShellWidth j ≤ 2 ^ j := by
  cases j with
  | zero => simp
  | succ i => exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ i)

/-- The shell `I^{sh}_j` is the half-open interval `[α_j, α_j + W_j)`, with `α_0 = 0` and
`α_j = 2^{j-1}` for `j ≥ 1`. -/
theorem mxShShell_eq_Ico_shShellWidth (j : ℕ) :
    ∃ α : ℝ, 0 ≤ α ∧ mxShShell j = Set.Ico α (α + shShellWidth j) := by
  cases j with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ i =>
    refine ⟨2 ^ i, by positivity, ?_⟩
    rw [mxShShell_succ, shShellWidth_succ, pow_succ]
    push_cast
    congr 1
    ring

end CollatzPosDens
