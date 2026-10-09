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
# The residual of the ordinary-clock constant

With $\kappa = 34881/10000$ and the decimal lower approximation $693147180/10^9$ of $\log 2$,
this file proves the exact rational identity
$$\frac{693147180}{10^9}\Bigl(\frac{523}{50}-\frac{517}{200}\kappa\Bigr)-\frac{\kappa}{12288}-1
  = \frac{43510569153}{400000000000000}.$$

## Main results

* `CollatzPosDens.ckOrdinaryResidual_eq`: the identity above, in any field of
  characteristic zero.

## Implementation notes

The identity is stated in an arbitrary field of characteristic zero (in particular `ℝ` and `ℚ`)
rather than only for real numbers; it holds by the same rational computation.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of the ordinary-clock residual
`693147180/10^9 · (523/50 - 517/200 · κ) - κ / 12288 - 1` with `κ = 34881/10000`. -/
@[collatz_pos_dens "lem_ck_ordinary_residual"]
theorem ckOrdinaryResidual_eq {K : Type*} [Field K] [CharZero K] :
    (693147180 / 10 ^ 9 : K) * (523 / 50 - 517 / 200 * (34881 / 10000))
        - (34881 / 10000 : K) / 12288 - 1
      = 43510569153 / 400000000000000 := by
  norm_num

end CollatzPosDens
