/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Budget
public import CollatzPosDens.Transfer.S02BudgetPlus

/-!
# The budget is at most the rounded budget

For each Fourier index `ι`, the budget `Bud(ι)` and the rounded budget `Bud⁺(ι)` differ only in
their adaptive packing term, so `Bud⁺(ι) - Bud(ι) = (c_cont(ι) - 1/P_W(ι)) (Π⁺_ad(ι) - Π_ad(ι))`.
The second factor is nonnegative since `Π_ad(ι) ≤ Π⁺_ad(ι)`. For the first,
`x_W(o) = 4838645241 / 10⁹ > 0` and `x_W(b) = 4476609 / 10⁶ > 0`, so every term of the
Taylor sum `P_W(ι)` is nonnegative and its `j = 0` term is `1`; hence `P_W(ι) ≥ 1`,
`1/P_W(ι) ≤ 1`, and `c_cont(ι) - 1/P_W(ι) ≥ c_cont(ι) - 1 > 0`, as
`c_cont(o) = 14009206687631 / (5 · 10¹¹) > 1` and `c_cont(b) = 7245014059 / (5 · 10⁸) > 1`.
The product is therefore nonnegative, so `Bud(ι) ≤ Bud⁺(ι)`.

## Main results

* `CollatzPosDens.Bud_le_budPlus`: `Bud(ι) ≤ Bud⁺(ι)` for every Fourier index `ι`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The budget is at most the rounded budget: `Bud(ι) ≤ Bud⁺(ι)`. -/
@[collatz_pos_dens "lem_s02_budget_le"]
theorem Bud_le_budPlus (ι : FIndex) : Bud ι ≤ budPlus ι := by
  have h : budPlus ι - Bud ι = (ccont ι - 1 / PW ι) * (piAdPlus ι - piAd ι) := by
    rw [budPlus_def, Bud_def]
    ring
  have := mul_nonneg (ccont_sub_inv_PW_pos ι).le (sub_nonneg.2 (piAd_le_piAdPlus ι))
  linarith

end CollatzPosDens
