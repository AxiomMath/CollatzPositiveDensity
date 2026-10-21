/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Table

/-!
# Range of the height-seventeen cost table

For integers `c, o` and `m`, the cost table `ct_{c,o}(m)` (`CollatzPosDens.c3H17Table`) lies in the
unit interval `[0, 1]`.

The number `1` is among the listed numbers whose least is the table, so `ct_{c,o}(m) ≤ 1`. Every
listed number is nonnegative: `1 - δ'_{c,o} ≥ 2^{-16}` (`CollatzPosDens.c3NarrowDeficit_le_cap`),
`Ū_c ≥ 0` (`CollatzPosDens.c3H17CapUp_nonneg`), `ℓ_c ≥ 0` (`CollatzPosDens.trLipConst_nonneg`),
`𝖫_o ≥ 0` (`CollatzPosDens.c3H17Lip_nonneg`) and `cf⁺_o(9m) ≥ 0`
(`CollatzPosDens.c3H17Node_nonneg`), and a ceiling of a nonnegative rational is nonnegative.

## Main results

* `CollatzPosDens.c3H17Table_mem_Icc`: `0 ≤ ct_{c,o}(m) ≤ 1`.

## Implementation notes

The bound is usually stated for `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and odd `m`; each listed number is
nonnegative for all integers `c, o, m`, so the bound holds, with the same proof, for all of them,
and is stated so.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The height-seventeen cost table is nonnegative: `0 ≤ ct_{c,o}(m)`. -/
theorem c3H17Table_nonneg (c o m : ℤ) : 0 ≤ c3H17Table c o m := by
  have hU := c3H17CapUp_nonneg c ((m : ℚ) / 2 ^ o)
  have hℓ : 0 ≤ trLipConst c * (2 : ℚ) ^ (-o) :=
    mul_nonneg (trLipConst_nonneg c) (zpow_nonneg (by norm_num) _)
  have hceil {x : ℚ} (hx : 0 ≤ x) : 0 ≤ (⌈(10 ^ 8 : ℚ) * x⌉ : ℚ) / 10 ^ 8 := by
    have : (0 : ℤ) ≤ ⌈(10 ^ 8 : ℚ) * x⌉ := Int.ceil_nonneg (by positivity)
    have : (0 : ℚ) ≤ (⌈(10 ^ 8 : ℚ) * x⌉ : ℚ) := by exact_mod_cast this
    positivity
  refine le_c3H17Table zero_le_one (fun _ => ?_) (fun _ => ?_) (fun _ => ?_)
  · exact sub_nonneg.mpr (c3NarrowDeficit_lt_one c o).le
  · exact add_nonneg hU (hceil (mul_nonneg (by norm_num) hℓ))
  · refine add_nonneg (hceil (mul_nonneg hU (c3H17Node_nonneg o (9 * m)))) (hceil ?_)
    exact mul_nonneg (by norm_num) (add_nonneg hℓ (mul_nonneg (by norm_num) (c3H17Lip_nonneg o)))

/-- **Range of the cost table.** For all integers `c, o, m`, `0 ≤ ct_{c,o}(m) ≤ 1`. -/
@[collatz_pos_dens "lem_c3_h17_table_range"]
theorem c3H17Table_mem_Icc (c o m : ℤ) : c3H17Table c o m ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨c3H17Table_nonneg c o m, c3H17Table_le_one c o m⟩

end CollatzPosDens
