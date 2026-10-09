/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.DyadicReduction

/-!
# The kernel of the dyadic reduction modulo `3^T`

A dyadic rational `q ∈ ℤ[1/2]` whose reduction `[q]_T` modulo `3^T` vanishes is divisible by
`3^T` inside `ℤ[1/2]`: writing `q = a / 2^e`, the residue `[2]_T` is a unit, so `[a]_T = 0`,
that is `3^T ∣ a`, and `q = 3^T · ((a / 3^T) / 2^e)`.

## Main results

* `CollatzPosDens.exists_eq_three_pow_mul_of_dyadicRed_eq_zero`: if `[q]_T = 0` then
  `q = 3^T q'` for some `q' ∈ ℤ[1/2]`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If the reduction `[q]_T` of a dyadic rational `q` modulo `3^T` is zero, then
`q = 3^T q'` for some dyadic rational `q'`. -/
@[collatz_pos_dens "lem_mx_dyadic_kernel"]
theorem exists_eq_three_pow_mul_of_dyadicRed_eq_zero {T : ℕ} {q : dyadicRationals}
    (hq : dyadicRed T q = 0) : ∃ q' : dyadicRationals, q = 3 ^ T * q' := by
  obtain ⟨n, e, hne⟩ := mem_dyadicRationals.1 q.2
  have hq' : q = ⟨n / 2 ^ e, intCast_div_two_pow_mem n e⟩ := Subtype.ext hne
  rw [hq', dyadicRed_div_two_pow] at hq
  have hu : IsUnit ((2 : ResidueGroup T)⁻¹ ^ e) := by
    obtain ⟨u, hu⟩ := isUnit_two_residueGroup T
    rw [← hu]
    exact (ZMod.inv_coe_unit u ▸ (u⁻¹).isUnit).pow e
  have hn : ((n : ℤ) : ResidueGroup T) = 0 := (hu.mul_left_eq_zero).1 hq
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hn
  obtain ⟨m, rfl⟩ := hn
  refine ⟨⟨m / 2 ^ e, intCast_div_two_pow_mem m e⟩, Subtype.ext ?_⟩
  rw [hq']
  have h3 : ((3 : dyadicRationals) : ℚ) = 3 := rfl
  simp [h3, mul_div_assoc]

end CollatzPosDens
