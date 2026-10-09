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
# The final generation threshold `J_*`

This file defines the final generation threshold
$$J_* = \max\bigl(N_* + N_{\mathrm t},\ 200\max(\mathrm{lg}(m) - 1, 0),\ 20 \cdot 10^9\bigr),$$
where `N_*` is the generation threshold, `N_t` the terminal threshold, `m` the fixed modulus
exponent and `lg` the binary ceiling logarithm.

## Main definitions

* `CollatzPosDens.finalGenerationThresholdOf`: the expression
  `max (N + T) (max (200 * (lg m - 1)) (20 * 10 ^ 9))` in parameters `N`, `T`, `m`.
* `CollatzPosDens.finalGenerationThreshold`: the threshold `J_*`, its value at `N = N_*`,
  `T = N_t` and `m = m`.

## Main results

* `CollatzPosDens.finalGenerationThreshold_def`: the defining formula of `J_*`.
* `CollatzPosDens.add_le_finalGenerationThreshold`: `N_* + N_t ≤ J_*`.
* `CollatzPosDens.lg_sub_le_finalGenerationThreshold`: `200 * (lg m - 1) ≤ J_*`.
* `CollatzPosDens.le_finalGenerationThreshold`: `20 * 10 ^ 9 ≤ J_*`.
* `CollatzPosDens.finalGenerationThreshold_pos`: `0 < J_*`.

## Implementation notes

The threshold is a natural number, being a generation index. The positive part `max (lg m - 1, 0)`
is the truncated subtraction of `ℕ`. Since `N_*`, `N_t` and `m` are far too large to be evaluated,
`finalGenerationThreshold` is irreducible and is characterised by `finalGenerationThreshold_def`.

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
`J_* = max (N_* + N_t) (max (200 * (lg m - 1)) (20 * 10 ^ 9))`. -/
@[collatz_pos_dens "def_Jstar", irreducible]
noncomputable def finalGenerationThreshold : ℕ :=
  finalGenerationThresholdOf generationThreshold terminalThreshold modulusExponent

/-- `J_*` is `finalGenerationThresholdOf` at `N_*`, `N_t` and `m`. -/
theorem finalGenerationThreshold_eq_finalGenerationThresholdOf :
    finalGenerationThreshold =
      finalGenerationThresholdOf generationThreshold terminalThreshold modulusExponent := by
  unfold finalGenerationThreshold
  rfl

/-- The defining formula `J_* = max (N_* + N_t) (max (200 * (lg m - 1)) (20 * 10 ^ 9))`. -/
theorem finalGenerationThreshold_def :
    finalGenerationThreshold = max (generationThreshold + terminalThreshold)
      (max (200 * (lg modulusExponent - 1)) (20 * 10 ^ 9)) :=
  finalGenerationThreshold_eq_finalGenerationThresholdOf.trans
    (finalGenerationThresholdOf_def _ _ _)

/-- `N_* + N_t ≤ J_*`. -/
theorem add_le_finalGenerationThreshold :
    generationThreshold + terminalThreshold ≤ finalGenerationThreshold :=
  finalGenerationThreshold_eq_finalGenerationThresholdOf ▸
    add_le_finalGenerationThresholdOf _ _ _

/-- `200 * (lg m - 1) ≤ J_*`. -/
theorem lg_sub_le_finalGenerationThreshold :
    200 * (lg modulusExponent - 1) ≤ finalGenerationThreshold :=
  finalGenerationThreshold_eq_finalGenerationThresholdOf ▸
    lg_sub_le_finalGenerationThresholdOf _ _ _

/-- `20 * 10 ^ 9 ≤ J_*`. -/
theorem le_finalGenerationThreshold : 20 * 10 ^ 9 ≤ finalGenerationThreshold :=
  finalGenerationThreshold_eq_finalGenerationThresholdOf ▸ le_finalGenerationThresholdOf _ _ _

/-- `J_*` is positive. -/
theorem finalGenerationThreshold_pos : 0 < finalGenerationThreshold :=
  lt_of_lt_of_le (by norm_num) le_finalGenerationThreshold

end CollatzPosDens
