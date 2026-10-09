/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxSliceGate
public import CollatzPosDens.Mixing.MxGateDisjoint

/-!
# Total mass of the head gates

For every integer `n ≥ 1`,
$$\sum_{k=0}^{n-1}\sum_{l=0}^{2n-1}\mathbf{p}(\mathrm{Hd}(n,k,l)) \le 1.$$

For `k < n`, the slice gate `Sl(n, k, l)` is the set of words of length `n` whose prefix of
length `k + 1` lies in `Hd(n, k, l)`, so by the marginal identity `geomMass_setOf_take_mem` it
has the same mass as the head gate. The slice gates are pairwise disjoint subsets of
`ℤ_{≥1}^n`, whose mass is `1`.

## Main results

* `CollatzPosDens.mxGateMassSum_finset_le`: for any finite set `s` of indices `(k, l)` with
  `k < n`, `∑_{(k, l) ∈ s} 𝐩(Hd(n, k, l)) ≤ 1`.
* `CollatzPosDens.mxGateMassSum_le_one`: `∑_{k<n} ∑_{l<2n} 𝐩(Hd(n, k, l)) ≤ 1`.

## Implementation notes

The hypothesis `n ≥ 1` is not needed: for `n = 0` the outer sum is empty. The bound is proved
for an arbitrary finite set of indices `(k, l)` with `k < n`, of which the range `0 ≤ k < n`,
`0 ≤ l < 2n` is one instance.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For any finite set `s` of indices `(k, l)` with `k < n`,
`∑_{(k, l) ∈ s} 𝐩(Hd(n, k, l)) ≤ 1`. -/
theorem mxGateMassSum_finset_le (n : ℕ) (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, p.1 < n) :
    ∑ p ∈ s, geomMass (mxHeadGate n p.1 p.2) ≤ 1 := by
  calc ∑ p ∈ s, geomMass (mxHeadGate n p.1 p.2)
      = ∑ p ∈ s, geomMass (mxSliceGate n p.1 p.2) :=
        Finset.sum_congr rfl fun p hp => (geomMass_setOf_take_mem (hs p hp)
          fun _ hv => length_of_mem_mxHeadGate hv).symm
    _ = geomMass (⋃ p ∈ s, mxSliceGate n p.1 p.2) := by
        simp_rw [geomMass_eq_tsum_indicator]
        rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        congr 1
        funext w
        rw [Finset.indicator_biUnion_apply]
        exact pairwiseDisjoint_mxSliceGate n _
    _ ≤ geomMass {w : Word | w.length = n} :=
        geomMass_mono (Set.iUnion₂_subset fun _ _ _ hw => length_of_mem_mxSliceGate hw)
    _ = 1 := geomMass_setOf_length_eq n

/-- **Total mass of the head gates.** For every `n`,
`∑_{k=0}^{n-1} ∑_{l=0}^{2n-1} 𝐩(Hd(n, k, l)) ≤ 1`. -/
@[collatz_pos_dens "lem_mx_gate_mass_sum"]
theorem mxGateMassSum_le_one (n : ℕ) :
    ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range (2 * n), geomMass (mxHeadGate n k l) ≤ 1 := by
  rw [← Finset.sum_product']
  exact mxGateMassSum_finset_le n _ fun p hp => Finset.mem_range.mp (Finset.mem_product.mp hp).1

end CollatzPosDens
