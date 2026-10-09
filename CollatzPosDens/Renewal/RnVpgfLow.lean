/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnVpgf
public import CollatzPosDens.Renewal.RnHoldVpgf

/-!
# The vertical generating function of a hold at `4095/4096`

At `v = 4095/4096` the non-closing weight
`v² / (2 - v)² - (3/16) v⁴ - (1/8) v⁵ = 106338258257995682080077825/154818071997770485540585472`
is below `1`, so the closed form of `𝖵` gives the exact rational value `𝖵(v) = a / b` with
`a = 48328698012322974813669375` and `b = 48479813739774803460507647`. The inequality
`𝖵(v)^10 < v^127` is then the integer inequality `a^10 · 4096^127 < b^10 · 4095^127`.

## Main results

* `CollatzPosDens.holdVpgf_low_eq`: `𝖵(4095/4096) = a / b`.
* `CollatzPosDens.holdVpgf_low_pow_lt`: `𝖵(4095/4096)^10 < (4095/4096)^127`.

## Implementation notes

`𝖵` takes values in `[0, ∞]`; the right-hand side `(4095/4096)^127` is the real power embedded
by `ENNReal.ofReal`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The exact value `𝖵(4095/4096) = 48328698012322974813669375/48479813739774803460507647`. -/
theorem holdVpgf_low_eq :
    holdVpgf (4095 / 4096) =
      ENNReal.ofReal (48328698012322974813669375 / 48479813739774803460507647) := by
  rw [holdVpgf_eq (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The vertical generating function satisfies `𝖵(4095/4096)^10 < (4095/4096)^127`. -/
@[collatz_pos_dens "lem_rn_vpgf_low"]
theorem holdVpgf_low_pow_lt :
    holdVpgf (4095 / 4096) ^ 10 < ENNReal.ofReal ((4095 / 4096) ^ 127) := by
  rw [holdVpgf_low_eq, ← ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

end CollatzPosDens
