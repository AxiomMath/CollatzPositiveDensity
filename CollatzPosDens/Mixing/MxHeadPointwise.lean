/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxHeadMass
public import CollatzPosDens.Mixing.MxHeadInjective

/-!
# A pointwise bound on the head mass

For all `n, k, l ∈ ℕ` and `y ∈ G_n`, the head mass satisfies `Hm_{n,k,l}(y) ≤ 2^{-l}`.

Heads in `Hd(n, k, l)` are separated modulo `3 ^ n`, so at most one head `h` has
`[off(h)]_n = y`; every head has valuation sum `A(h) = l`, so its weight is `2^{-l}`. The sum
defining `Hm_{n,k,l}(y)` therefore has at most one term, of value `2^{-l}`.

## Main results

* `CollatzPosDens.mxHeadMass_le_two_inv_pow`: `Hm_{n,k,l}(y) ≤ 2^{-l}`.

## Implementation notes

The weight `2^{-l}` is written `2⁻¹ ^ l`, as in the definition of the head mass. The bound
holds for every natural number `n`, including `n = 0`, since neither the separation of heads
nor the computation of the weights requires `n ≥ 1`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Pointwise bound on the head mass.** For all `n, k, l ∈ ℕ` and `y ∈ G_n`,
`Hm_{n,k,l}(y) ≤ 2^{-l}`. -/
@[collatz_pos_dens "lem_mx_head_pointwise"]
theorem mxHeadMass_le_two_inv_pow (n k l : ℕ) (y : ResidueGroup n) :
    mxHeadMass n k l y ≤ (2⁻¹ : ℝ) ^ l := by
  rw [mxHeadMass_def]
  set s := {h ∈ (mxHeadGate_finite n k l).toFinset |
    dyadicRed n ⟨off h, off_mem_dyadicRationals h⟩ = y} with hs
  have hval : ∀ h ∈ s, (2⁻¹ : ℝ) ^ h.valSum = (2⁻¹ : ℝ) ^ l := by
    intro h hh
    rw [hs, Finset.mem_filter, Set.Finite.mem_toFinset] at hh
    rw [valSum_of_mem_mxHeadGate hh.1]
  have hcard : s.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hs, Finset.mem_filter, Set.Finite.mem_toFinset] at ha hb
    exact eq_of_dyadicRed_off_eq_of_mem_mxHeadGate ha.1 hb.1 (ha.2.trans hb.2.symm)
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  calc (s.card : ℝ) * (2⁻¹ : ℝ) ^ l ≤ 1 * (2⁻¹ : ℝ) ^ l := by
        gcongr; exact_mod_cast hcard
    _ = (2⁻¹ : ℝ) ^ l := one_mul _

end CollatzPosDens
