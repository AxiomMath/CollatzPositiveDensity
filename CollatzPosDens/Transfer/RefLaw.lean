/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.DyadicReduction

/-!
# The reference law on the residue spaces

The reference weights `μ_q : G_q → [0, ∞]` are defined recursively by `μ_0(0) = 1` and, for
`y ∈ G_{q+1}`,
$$\mu_{q+1}(y) = \sum_{a \ge 1} 2^{-a} \sum_{z \in G_q,\ [2^{-a}(3\tilde z + 1)]_{q+1} = y}
  \mu_q(z),$$
where `z̃` is the least nonnegative representative of `z` and `[·]_{q+1}` is the reduction of
dyadic rationals modulo `3^{q+1}`. This is the law of the random residue `Y_q`, where `Y_0 = 0`
and `Y_{q+1} = 2^{-A_{q+1}}(3 Y_q + 1) mod 3^{q+1}` with independent `Pr(A_j = a) = 2^{-a}`;
it is Tao's Syracuse random variable `Syrac(ℤ/3^qℤ)`.

## Main definitions

* `CollatzPosDens.refStep q a z`: the residue `[2^{-a}(3 z̃ + 1)]_{q+1} ∈ G_{q+1}`.
* `CollatzPosDens.refLaw q`: the weights `μ_q : G_q → ℝ≥0∞`.

## Main results

* `CollatzPosDens.refStep_eq`: `[2^{-a}(3 z̃ + 1)]_{q+1} = (3 z̃ + 1) · (2⁻¹)^a` in `G_{q+1}`.
* `CollatzPosDens.refLaw_zero`: `μ_0(0) = 1`; `CollatzPosDens.refLaw_zero_apply`: `μ_0` is
  identically `1`.
* `CollatzPosDens.refLaw_succ`: the defining recursion, with the sum over `a ≥ 1`.

## Implementation notes

The weights take values in `ℝ≥0∞`, so that the infinite sum over `a` is always defined. In the
definition the index `a ≥ 1` is written as `a + 1` with `a : ℕ`; `refLaw_succ` restates the
recursion with the sum over all `a : ℕ` restricted to `1 ≤ a`. Since `G_0` has the single element
`0`, `μ_0` is the constant function `1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- For `z ∈ G_q`, the rational `(3 z̃ + 1) / 2^a` lies in `ℤ[1/2]`. -/
theorem refStep_mem (q a : ℕ) (z : ResidueGroup q) :
    ((((3 * z.val + 1 : ℕ) : ℤ) : ℚ) / 2 ^ a) ∈ dyadicRationals :=
  intCast_div_two_pow_mem _ a

/-- The Syracuse step `[2^{-a}(3 z̃ + 1)]_{q+1} ∈ G_{q+1}` of a residue `z ∈ G_q`, where `z̃` is
the least nonnegative representative of `z`. -/
@[collatz_pos_dens "def_ref_law"]
noncomputable def refStep (q a : ℕ) (z : ResidueGroup q) : ResidueGroup (q + 1) :=
  dyadicRed (q + 1) ⟨(((3 * z.val + 1 : ℕ) : ℤ) : ℚ) / 2 ^ a, refStep_mem q a z⟩

/-- The Syracuse step computed in `G_{q+1}`: `[2^{-a}(3 z̃ + 1)]_{q+1} = (3 z̃ + 1) · (2⁻¹)^a`. -/
theorem refStep_eq (q a : ℕ) (z : ResidueGroup q) :
    refStep q a z = (3 * (z.val : ResidueGroup (q + 1)) + 1) * 2⁻¹ ^ a := by
  rw [refStep, dyadicRed_div_two_pow]
  push_cast
  rfl

/-- The reference weights `μ_q : G_q → [0, ∞]`: `μ_0 = 1` on `G_0 = {0}`, and
`μ_{q+1}(y) = ∑_{a ≥ 1} 2^{-a} ∑_{z ∈ G_q, [2^{-a}(3 z̃ + 1)]_{q+1} = y} μ_q(z)`. -/
@[collatz_pos_dens "def_ref_law"]
noncomputable def refLaw : (q : ℕ) → ResidueGroup q → ℝ≥0∞
  | 0 => fun _ => 1
  | q + 1 => fun y => ∑' a : ℕ, 2⁻¹ ^ (a + 1) *
      ∑ z ∈ Finset.univ.filter (fun z => refStep q (a + 1) z = y), refLaw q z

/-- The initial condition `μ_0(0) = 1`. -/
theorem refLaw_zero : refLaw 0 0 = 1 := rfl

/-- `μ_0` is identically `1` on the one-point space `G_0`. -/
@[simp]
theorem refLaw_zero_apply (y : ResidueGroup 0) : refLaw 0 y = 1 := rfl

/-- The recursion as defined, with the index `a + 1` (`a : ℕ`) running over the positive
integers. -/
theorem refLaw_succ_apply (q : ℕ) (y : ResidueGroup (q + 1)) :
    refLaw (q + 1) y = ∑' a : ℕ, 2⁻¹ ^ (a + 1) *
      ∑ z ∈ Finset.univ.filter (fun z => refStep q (a + 1) z = y), refLaw q z := rfl

/-- The defining recursion of the reference law, with the sum over `a ≥ 1`:
`μ_{q+1}(y) = ∑_{a ≥ 1} 2^{-a} ∑_{z ∈ G_q, [2^{-a}(3 z̃ + 1)]_{q+1} = y} μ_q(z)`. -/
theorem refLaw_succ (q : ℕ) (y : ResidueGroup (q + 1)) :
    refLaw (q + 1) y = ∑' a : ℕ, if 1 ≤ a then 2⁻¹ ^ a *
      ∑ z ∈ Finset.univ.filter (fun z => refStep q a z = y), refLaw q z else 0 := by
  rw [refLaw_succ_apply]
  conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
  simp

end CollatzPosDens
