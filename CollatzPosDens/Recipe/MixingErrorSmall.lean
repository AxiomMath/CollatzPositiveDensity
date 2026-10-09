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

This file proves the numerical inequality
$$m^{9/8} > 2^{39}\,\mathcal{M}\,C$$
on the seed bound `𝓜`, the mixing coefficient `C` and the modulus exponent
`m = ⌊(2^{39} 𝓜 C)^{8/9}⌋₊ + 1`. With `y = (2^{39} 𝓜 C)^{8/9}` one has `y < m`, hence
`m^{9/8} > y^{9/8} = 2^{39} 𝓜 C` by strict monotonicity of `t ↦ t^{9/8}` on `[0, ∞)`.

## Main results

* `CollatzPosDens.lt_modulusExponentOf_rpow`: `x < (⌊x^{8/9}⌋₊ + 1)^{9/8}` for every real
  `x ≥ 0`.
* `CollatzPosDens.lt_modulusExponent_rpow`: `2^{39} 𝓜 C < m^{9/8}`.

## Implementation notes

The power `m^{9/8}` is Mathlib's real power `Real.rpow` of the natural number `m` cast to `ℝ`.

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

/-- The modulus exponent `m = modulusExponent` satisfies `2^39 𝓜 C < m ^ (9/8)`, where `𝓜` is
`seedBound` and `C` is `mixingConst`. -/
@[collatz_pos_dens "lem_mixing_error_small"]
theorem lt_modulusExponent_rpow :
    (2 : ℝ) ^ 39 * seedBound * mixingConst < (modulusExponent : ℝ) ^ (9 / 8 : ℝ) :=
  modulusExponent_eq_modulusExponentOf ▸ lt_modulusExponentOf_rpow modulusExponent_base_pos.le

end CollatzPosDens
