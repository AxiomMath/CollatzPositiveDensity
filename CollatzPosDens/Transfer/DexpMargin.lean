/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.Dexp
public import CollatzPosDens.Transfer.W
public import CollatzPosDens.OrdinaryTime.Log2Sharp

/-!
# The moment threshold margin

Beyond the moment threshold `Dexp = 2 ^ 33495` the logarithm is large enough that
`wStar * log m > 234 * Aexp`. Indeed `log m ≥ 33495 log 2 > 33495 · 693147180/10^9`, and
`(63/2500) · 33495 · 693147180/10^9 = 585.0675… > 585.0571… = 234 · 10241/4096`.

## Main results

* `CollatzPosDens.Dexp_margin`: for every real `m ≥ Dexp`, `234 * Aexp < wStar * log m`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- For every real `m ≥ Dexp`, `234 * Aexp < wStar * log m`. -/
@[collatz_pos_dens "lem_s02_Dexp_margin"]
theorem Dexp_margin {m : ℝ} (hm : (Dexp : ℝ) ≤ m) :
    234 * (Aexp : ℝ) < (wStar : ℝ) * log m := by
  have hlog : (33495 : ℝ) * log 2 ≤ log m := by
    have h := log_le_log (Dexp_cast_pos (R := ℝ)) hm
    rwa [Dexp_cast, log_pow, Nat.cast_ofNat] at h
  rw [Aexp_cast, wStar_cast]
  have h2 := log_two_gt_sharp
  nlinarith

end CollatzPosDens
