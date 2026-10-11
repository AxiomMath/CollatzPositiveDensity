/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.Nt
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Recipe.Clog

/-!
# The final generation threshold `J_*(s)`

For an endpoint parameter `s ≥ 1`, this file defines the final generation threshold
$$J_*(s) = \max\bigl(N_* + N_{\mathrm t},\ 200\max(\mathrm{lg}(m(s)) - 1, 0),\
  20 \cdot 10^9\bigr),$$
where `N_*` is the generation threshold, `N_t` the terminal threshold, `m(s)` the fixed modulus
exponent and `lg` the binary ceiling logarithm.

## Main definitions

* `CollatzPosDens.finalGenerationThresholdOf`: the expression
  `max (N + T) (max (200 * (lg m - 1)) (20 * 10 ^ 9))` in parameters `N`, `T`, `m`.
* `CollatzPosDens.finalGenerationThreshold`: the threshold `J_*(s)`, its value at `N = N_*`,
  `T = N_t` and `m = m(s)`.

## Main results

* `CollatzPosDens.finalGenerationThreshold_def`: the defining formula of `J_*(s)`.
* `CollatzPosDens.add_le_finalGenerationThreshold`: `N_* + N_t ≤ J_*(s)`.
* `CollatzPosDens.lg_sub_le_finalGenerationThreshold`: `200 * (lg m(s) - 1) ≤ J_*(s)`.
* `CollatzPosDens.le_finalGenerationThreshold`: `20 * 10 ^ 9 ≤ J_*(s)`.

## Implementation notes

The threshold is a natural number, since it is used as a generation index. The positive part
`max (lg m - 1, 0)` is the truncated subtraction of `ℕ`. Since `N_*`, `N_t` and `m(s)` are far too
large to be evaluated, `finalGenerationThreshold` is irreducible and is meant to be used through
`finalGenerationThreshold_def` and the bounds of this file.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `max (N + T) (max (200 * (lg m - 1)) (20 * 10 ^ 9))` with parameters
`N`, `T` and `m`. The final generation threshold `J_*` is its value at `N_*`, `N_t` and `m`. -/
def finalGenerationThresholdOf (N T m : ℕ) : ℕ :=
  max (N + T) (max (200 * (lg m - 1)) (20 * 10 ^ 9))

/-- The defining formula of `finalGenerationThresholdOf`. -/
theorem finalGenerationThresholdOf_def (N T m : ℕ) :
    finalGenerationThresholdOf N T m = max (N + T) (max (200 * (lg m - 1)) (20 * 10 ^ 9)) :=
  rfl

/-- `N + T ≤ finalGenerationThresholdOf N T m`. -/
theorem add_le_finalGenerationThresholdOf (N T m : ℕ) :
    N + T ≤ finalGenerationThresholdOf N T m :=
  le_max_left _ _

/-- `200 * (lg m - 1) ≤ finalGenerationThresholdOf N T m`. -/
theorem lg_sub_le_finalGenerationThresholdOf (N T m : ℕ) :
    200 * (lg m - 1) ≤ finalGenerationThresholdOf N T m :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- `20 * 10 ^ 9 ≤ finalGenerationThresholdOf N T m`. -/
theorem le_finalGenerationThresholdOf (N T m : ℕ) :
    20 * 10 ^ 9 ≤ finalGenerationThresholdOf N T m :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- The final generation threshold
`J_*(s) = max (N_* + N_t) (max (200 * (lg m(s) - 1)) (20 * 10 ^ 9))`. It is irreducible so that
tactics never try to evaluate it; use `finalGenerationThreshold_def`. -/
@[collatz_pos_dens "def_Jstar", irreducible]
noncomputable def finalGenerationThreshold (s : ℕ) : ℕ :=
  finalGenerationThresholdOf generationThreshold terminalThreshold (modulusExponent s)

/-- `J_*(s)` is `finalGenerationThresholdOf` at `N_*`, `N_t` and `m(s)`. -/
theorem finalGenerationThreshold_eq_finalGenerationThresholdOf (s : ℕ) :
    finalGenerationThreshold s =
      finalGenerationThresholdOf generationThreshold terminalThreshold (modulusExponent s) := by
  unfold finalGenerationThreshold
  rfl

/-- The defining formula `J_*(s) = max (N_* + N_t) (max (200 * (lg m(s) - 1)) (20 * 10 ^ 9))`. -/
theorem finalGenerationThreshold_def (s : ℕ) :
    finalGenerationThreshold s = max (generationThreshold + terminalThreshold)
      (max (200 * (lg (modulusExponent s) - 1)) (20 * 10 ^ 9)) :=
  (finalGenerationThreshold_eq_finalGenerationThresholdOf s).trans
    (finalGenerationThresholdOf_def _ _ _)

/-- `N_* + N_t ≤ J_*(s)`. -/
theorem add_le_finalGenerationThreshold (s : ℕ) :
    generationThreshold + terminalThreshold ≤ finalGenerationThreshold s :=
  (finalGenerationThreshold_eq_finalGenerationThresholdOf s) ▸
    add_le_finalGenerationThresholdOf _ _ _

/-- `200 * (lg m(s) - 1) ≤ J_*(s)`. -/
theorem lg_sub_le_finalGenerationThreshold (s : ℕ) :
    200 * (lg (modulusExponent s) - 1) ≤ finalGenerationThreshold s :=
  (finalGenerationThreshold_eq_finalGenerationThresholdOf s) ▸
    lg_sub_le_finalGenerationThresholdOf _ _ _

/-- `20 * 10 ^ 9 ≤ J_*(s)`. -/
theorem le_finalGenerationThreshold (s : ℕ) : 20 * 10 ^ 9 ≤ finalGenerationThreshold s :=
  (finalGenerationThreshold_eq_finalGenerationThresholdOf s) ▸
    le_finalGenerationThresholdOf _ _ _

/-- `J_*(s)` is positive. -/
theorem finalGenerationThreshold_pos (s : ℕ) : 0 < finalGenerationThreshold s :=
  lt_of_lt_of_le (by norm_num) (le_finalGenerationThreshold s)

end CollatzPosDens
