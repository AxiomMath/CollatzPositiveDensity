/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Monotone.MoRateSqrt

/-!
# A threshold on `m` bounding `moRate A m` by `w / 32`

Let `A ≥ 0` and `w > 0` be reals and let `m` be a natural number with `m ≥ (256A/w)^2 + 2`.
Then `moRate A m ≤ w/32`. Indeed `m ≥ 2` and `√m ≥ 256A/w`, so the bound
`moRate A m ≤ 8A/√m` of `CollatzPosDens.moRate_le_div_sqrt` gives
`moRate A m ≤ 8A·w/(256A) = w/32` when `A > 0`, and `moRate A m ≤ 0` when `A = 0`.

## Main results

* `CollatzPosDens.moRate_le_div_thirtyTwo`: `moRate A m ≤ w / 32` for `0 ≤ A`, `0 < w`
  and `(256 A / w)^2 + 2 ≤ m`.

## Implementation notes

Since `m ≥ 2`, the integer `m` is taken in `ℕ`, the domain of `moRate`; the hypothesis on `m`
is stated in `ℝ`.

## References

* [Mazur, *Collatz positive density*], §8.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- For reals `A ≥ 0`, `w > 0` and a natural number `m ≥ (256A/w)^2 + 2`, `moRate A m ≤ w/32`. -/
@[collatz_pos_dens "lem_mo_rate_D1"]
theorem moRate_le_div_thirtyTwo {A w : ℝ} (hA : 0 ≤ A) (hw : 0 < w) {m : ℕ}
    (hm : (256 * A / w) ^ 2 + 2 ≤ (m : ℝ)) :
    moRate A m ≤ w / 32 := by
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by nlinarith [sq_nonneg (256 * A / w)]
    exact_mod_cast this
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm1)
  have hsqrt : 256 * A / w ≤ Real.sqrt m :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hsqrt' : 256 * A ≤ w * Real.sqrt m := by
    rw [div_le_iff₀ hw] at hsqrt
    linarith
  calc moRate A m ≤ 8 * A / Real.sqrt m := moRate_le_div_sqrt hA hm1
    _ ≤ w / 32 := by
      rw [div_le_div_iff₀ hs (by norm_num)]
      linarith

end CollatzPosDens
