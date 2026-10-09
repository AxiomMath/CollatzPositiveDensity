/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Inv
public import CollatzPosDens.Attr

/-!
# The residual of the accelerated-clock constant

With the stopping-time coefficient $c_s = 28559/100000$ and $\kappa = 34881/10000$, so that
$c_s\kappa = 996166479/10^9$, this file proves the exact rational identity
$$\Bigl(c_s\kappa-\frac1{9000}\Bigr)\frac{287682}{10^6}-\frac{c_s\kappa}{12288}-c_s
  -\frac{219}{250000} = \frac{25365007801}{192000000000000000}.$$

## Main results

* `CollatzPosDens.ckAccelResidual_eq`: the identity above, in any field of characteristic
  zero.

## Implementation notes

The identity is stated in an arbitrary field of characteristic zero (in particular `ℝ` and `ℚ`)
rather than only for real numbers, since it holds there by the same rational computation.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of the accelerated-clock residual
`(c_s κ - 1/9000) · 287682/10^6 - c_s κ / 12288 - c_s - 219/250000`, with
`c_s = 28559/100000` and `κ = 34881/10000`. -/
@[collatz_pos_dens "lem_ck_accel_residual"]
theorem ckAccelResidual_eq {K : Type*} [Field K] [CharZero K] :
    ((28559 / 100000 : K) * (34881 / 10000) - 1 / 9000) * (287682 / 10 ^ 6)
        - (28559 / 100000 : K) * (34881 / 10000) / 12288 - 28559 / 100000 - 219 / 250000
      = 25365007801 / 192000000000000000 := by
  norm_num

end CollatzPosDens
