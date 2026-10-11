/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Transfer.MixingConst

/-!
# The modulus exponent dominates the mixing error

This file proves, for every endpoint `s`, the numerical inequality
$$m(s)^{9/8} > 2^{39}\,\mathcal{M}(s)\,C$$
on the seed allowance `𝓜(s)`, the mixing coefficient `C` and the modulus exponent
`m(s) = ⌊(2^{39} 𝓜(s) C)^{8/9}⌋₊ + 1`. With `y = (2^{39} 𝓜(s) C)^{8/9}` one has `y < m(s)`,
hence `m(s)^{9/8} > y^{9/8} = 2^{39} 𝓜(s) C` by strict monotonicity of `t ↦ t^{9/8}` on
`[0, ∞)`.

## Main results

* `CollatzPosDens.lt_modulusExponentOf_rpow`: `x < (⌊x^{8/9}⌋₊ + 1)^{9/8}` for every real
  `x ≥ 0`.
* `CollatzPosDens.lt_modulusExponent_rpow`: `2^{39} 𝓜(s) C < m(s)^{9/8}`.

## Implementation notes

The power `m(s)^{9/8}` is Mathlib's real power `Real.rpow` of the natural number `m(s)` cast
to `ℝ`. Mazur states the inequality for `s ≥ 1`; only `2^{39} 𝓜(s) C ≥ 0` is used, so
it is stated here for every `s : ℕ` (for `s = 0` the left side vanishes).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `0 ≤ x`, `x < (modulusExponentOf x) ^ (9/8)`, where
`modulusExponentOf x = ⌊x ^ (8/9)⌋₊ + 1`. -/
theorem lt_modulusExponentOf_rpow {x : ℝ} (hx : 0 ≤ x) :
    x < (modulusExponentOf x : ℝ) ^ (9 / 8 : ℝ) := by
  have h := Real.rpow_lt_rpow (Real.rpow_nonneg hx (8 / 9 : ℝ)) (lt_modulusExponentOf x)
    (by norm_num : (0 : ℝ) < 9 / 8)
  rwa [← Real.rpow_mul hx, show (8 / 9 : ℝ) * (9 / 8) = 1 by norm_num, Real.rpow_one] at h

/-- **The strict root**: `m(s) ^ (9/8) > 2^39 𝓜(s) C` for every endpoint `s`. -/
@[collatz_pos_dens "lem_mixing_error_small"]
theorem lt_modulusExponent_rpow (s : ℕ) :
    (2 : ℝ) ^ 39 * seedBound s * mixingConst < (modulusExponent s : ℝ) ^ (9 / 8 : ℝ) :=
  modulusExponent_eq_modulusExponentOf s ▸
    lt_modulusExponentOf_rpow (modulusExponent_base_nonneg s)

end CollatzPosDens
