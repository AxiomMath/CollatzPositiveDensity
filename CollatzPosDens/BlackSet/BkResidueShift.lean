/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkThetaResidue

/-!
# Shifting the angle residue

For points `a, q ∈ 𝒫` with `j(a) ≤ j(q)` and `l(q) ≤ l(a)`, the angle residues are related by
multiplication by the positive integer `h = 9^{j(q)-j(a)} 2^{l(a)-l(q)}`: `r(q) = h · r(a)` in
`G_n`. This holds already for the dyadic rationals `3^{2(j-1)} 2^{1-l}`, and the reduction
`[·]_n` is a ring homomorphism.

## Main results

* `CollatzPosDens.bkThetaDyadic_shift`: `3^{2(j(q)-1)} 2^{1-l(q)} = h · 3^{2(j(a)-1)} 2^{1-l(a)}`
  in `ℤ[1/2]`.
* `CollatzPosDens.bkThetaResidue_shift`: `r_{n,ξ}(q) = h · r_{n,ξ}(a)` in `G_n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The dyadic identity `3^{2(j(q)-1)} 2^{1-l(q)} = 9^{j(q)-j(a)} 2^{l(a)-l(q)} ·
3^{2(j(a)-1)} 2^{1-l(a)}` in `ℤ[1/2]`, for `a, q ∈ 𝒫` with `j(a) ≤ j(q)` and `l(q) ≤ l(a)`. -/
theorem bkThetaDyadic_shift {a q : ℤ × ℤ} (ha : a ∈ bkPoints) (hq : q ∈ bkPoints)
    (hj : bkJ a ≤ bkJ q) (hl : bkL q ≤ bkL a) :
    bkThetaDyadic q =
      ((9 ^ (bkJ q - bkJ a).toNat * 2 ^ (bkL a - bkL q).toNat : ℕ) : dyadicRationals) *
        bkThetaDyadic a := by
  apply Subtype.ext
  change (bkThetaDyadic q : ℚ) = ((_ : ℕ) : ℚ) * (bkThetaDyadic a : ℚ)
  rw [coe_bkThetaDyadic hq, coe_bkThetaDyadic ha]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
    Int.toNat_of_nonneg (by omega)]
  have h9 : (9 : ℚ) = 3 ^ (2 : ℤ) := by norm_num
  rw [h9, ← zpow_mul]
  have h3 : (2 * (bkJ q - 1)) = 2 * (bkJ q - bkJ a) + 2 * (bkJ a - 1) := by ring
  have h2 : 1 - bkL q = (bkL a - bkL q) + (1 - bkL a) := by ring
  rw [h3, h2, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]
  ring

/-- **Residue shift.** For `a, q ∈ 𝒫` with `j(a) ≤ j(q)` and `l(q) ≤ l(a)`, and
`h = 9^{j(q)-j(a)} 2^{l(a)-l(q)} ∈ ℤ_{≥1}`, the angle residues satisfy `r(q) = h · r(a)` in
`G_n`. -/
@[collatz_pos_dens "lem_bk_residue_shift"]
theorem bkThetaResidue_shift (n : ℕ) (ξ : ResidueGroup n) {a q : ℤ × ℤ} (ha : a ∈ bkPoints)
    (hq : q ∈ bkPoints) (hj : bkJ a ≤ bkJ q) (hl : bkL q ≤ bkL a) :
    bkThetaResidue n ξ q =
      ((9 ^ (bkJ q - bkJ a).toNat * 2 ^ (bkL a - bkL q).toNat : ℕ) : ResidueGroup n) *
        bkThetaResidue n ξ a := by
  rw [bkThetaResidue_def, bkThetaResidue_def, bkThetaDyadic_shift ha hq hj hl, map_mul,
    map_natCast, mul_assoc]

end CollatzPosDens
