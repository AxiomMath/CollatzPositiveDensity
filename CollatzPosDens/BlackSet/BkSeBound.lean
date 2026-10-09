/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSeWeight
public import CollatzPosDens.BlackSet.BkTheta
public import CollatzPosDens.BlackSet.BkResidueShift
public import CollatzPosDens.BlackSet.BkSfrScaleBound

/-!
# Bounding the angle along a south-east step

For points `a, q ∈ 𝒫` with `j(a) ≤ j(q)` and `l(q) ≤ l(a)`, the angle of `q` is controlled by the
angle of `a`: `|ϑ(q)| ≤ e^{se(a, q)} |ϑ(a)|`. Indeed `r(q) = h · r(a)` with
`h = 9^{j(q)-j(a)} 2^{l(a)-l(q)} = e^{se(a, q)}`, and the signed fractional part satisfies
`|sfr (h z)| ≤ h |sfr z|`.

## Main results

* `CollatzPosDens.abs_bkTheta_le_exp_bkSe_mul`: `|ϑ_{n,ξ}(q)| ≤ e^{se(a, q)} |ϑ_{n,ξ}(a)|`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `a, q ∈ 𝒫` with `j(a) ≤ j(q)` and `l(q) ≤ l(a)`, the angles satisfy
`|ϑ_{n,ξ}(q)| ≤ e^{se(a, q)} |ϑ_{n,ξ}(a)|`. -/
@[collatz_pos_dens "lem_bk_se_bound"]
theorem abs_bkTheta_le_exp_bkSe_mul (n : ℕ) (ξ : ResidueGroup n) {a q : ℤ × ℤ}
    (ha : a ∈ bkPoints) (hq : q ∈ bkPoints) (hj : bkJ a ≤ bkJ q) (hl : bkL q ≤ bkL a) :
    |bkTheta n ξ q| ≤ Real.exp (bkSe a q) * |bkTheta n ξ a| := by
  rw [exp_bkSe_eq_natCast hj hl, bkTheta_def, bkTheta_def, bkThetaResidue_shift n ξ ha hq hj hl]
  exact abs_sfr_natCast_mul_le _ _

end CollatzPosDens
