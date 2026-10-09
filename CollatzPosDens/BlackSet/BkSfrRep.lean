/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSignedFrac

/-!
# The signed fractional part of a small representative

If `m : ℤ` represents `z : ZMod N` and `|m| < N / 2`, then `sfr z = m / N`: the integer `m`
then satisfies `-N < 2m < N`, so it is the representative `ZMod.valMinAbs z` used to define
`sfr`.

## Main results

* `CollatzPosDens.sfr_eq_of_abs_lt`: `sfr z = m / N` whenever `(m : ZMod N) = z` and
  `|m| < N / 2`.

## Implementation notes

The source assumes `N ≥ 1` odd. Neither assumption is needed: `|m| < N / 2` already forces
`N > 0`, and oddness plays no role.

## References

* [Mazur, *Collatz positive density*], §5.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `m : ℤ` represents `z : ZMod N` and `|m| < N / 2`, then `sfr z = m / N`. -/
@[collatz_pos_dens "lem_bk_sfr_rep"]
theorem sfr_eq_of_abs_lt {N : ℕ} {z : ZMod N} {m : ℤ} (hm : (m : ZMod N) = z)
    (habs : |(m : ℝ)| < N / 2) : sfr z = (m : ℝ) / N := by
  have h2 : |(m : ℝ)| * 2 < N := by linarith
  have h2' : |m| * 2 < (N : ℤ) := by exact_mod_cast h2
  have hN : N ≠ 0 := by
    rintro rfl
    have := abs_nonneg m
    omega
  have : NeZero N := ⟨hN⟩
  exact sfr_eq_of_spec hm (by linarith [neg_abs_le m]) (by linarith [le_abs_self m])

end CollatzPosDens
