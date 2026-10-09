/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxSubmassUnion
public import CollatzPosDens.Mixing.MxTailLaw
public import CollatzPosDens.Mixing.MxGateDisjoint
public import CollatzPosDens.Mixing.MxGateUnion
public import CollatzPosDens.Mixing.MxGateWeightSum
public import CollatzPosDens.Mixing.MxHeadPointwise
public import CollatzPosDens.Mixing.MxSliceConvolution
public import CollatzPosDens.Mixing.MxSubdensity

/-!
# A pointwise cap on the gate subdensity

For every integer `n ≥ 2^131072` and `y ∈ G_n`, the gate subdensity satisfies
$$g_n(y) \le \tfrac{16}{3}\, n^{5633/2048}.$$

The gate union `𝒰_n` is the disjoint union of the slice gates `Sl(n, k, l)`, `k < n`, `l < 2n`,
so its submass at `y` is the sum of the slice submasses. A slice with empty head gate is empty.
Otherwise the slice submass is the convolution `∑_x Hm_{n,k,l}(x) Tl_{n,k,l}(y - x)`; the head
mass is pointwise at most `2^{-l}` and the tail law has total mass `∑_z μ_{n-k-1}(z) = 1`, so the
slice submass is at most `2^{-l}`. Summing, `g_n(y) ≤ (2/3) ∑ 3^n 2^{-l}` over the indices with
nonempty head gate, which is at most `(2/3) · 8 n^{5633/2048}` by
`mxGateWeightSum_le_of_sixteen_le`.

## Main results

* `CollatzPosDens.subMass_mxSliceGate_le_two_inv_pow`: `Sub^n_{Sl(n,k,l)}(y) ≤ 2^{-l}`.
* `CollatzPosDens.subMass_mxSliceGate_eq_zero_of_not_nonempty`: a slice with empty head gate
  has submass `0`.
* `CollatzPosDens.subMass_mxGateUnion_le_sum`: `Sub^n_{𝒰_n}(y) ≤ ∑ 2^{-l}` over the indices
  with nonempty head gate.
* `CollatzPosDens.mxSubdensity_le_of_sixteen_le`: the cap, for every `n ≥ 16`.
* `CollatzPosDens.mxSubdensity_le_cap`: the cap `g_n(y) ≤ (16/3) n^{5633/2048}` for
  `n ≥ 2^131072`.

## Implementation notes

The submasses are computed in `[0, ∞]` and transferred to `ℝ` at the end through `toReal`,
after the submass of `𝒰_n` has been shown finite. The bound holds as soon as
`mxGateWeightSum_le_of_sixteen_le` does, i.e. for every `n ≥ 16`; `mxSubdensity_le_cap` states it
under the hypothesis `n ≥ 2^131072`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The slice submass is at most `2^{-l}`: `Sub^n_{Sl(n,k,l)}(y) ≤ 2^{-l}` for `k < n`. -/
theorem subMass_mxSliceGate_le_two_inv_pow {n k l : ℕ} (hk : k < n) (y : ResidueGroup n) :
    subMass n (mxSliceGate n k l) y ≤ (2⁻¹ : ℝ≥0∞) ^ l := by
  rw [subMass_mxSliceGate_eq_sum hk]
  have hH : ∀ x, ENNReal.ofReal (mxHeadMass n k l x) ≤ (2⁻¹ : ℝ≥0∞) ^ l := fun x => by
    refine (ENNReal.ofReal_le_ofReal (mxHeadMass_le_two_inv_pow n k l x)).trans_eq ?_
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  calc ∑ x, ENNReal.ofReal (mxHeadMass n k l x) * tailLaw n k l (y - x)
      ≤ ∑ x, (2⁻¹ : ℝ≥0∞) ^ l * tailLaw n k l (y - x) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_left (hH x) _
    _ = (2⁻¹ : ℝ≥0∞) ^ l * ∑ x, tailLaw n k l x := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fintype.sum_equiv (Equiv.subLeft y) _ _ fun _ => rfl
    _ = (2⁻¹ : ℝ≥0∞) ^ l := by rw [sum_tailLaw_eq_one, mul_one]

/-- A slice gate with empty head gate is empty, so its submass vanishes. -/
theorem subMass_mxSliceGate_eq_zero_of_not_nonempty {n k l : ℕ}
    (h : ¬ (mxHeadGate n k l).Nonempty) (y : ResidueGroup n) :
    subMass n (mxSliceGate n k l) y = 0 := by
  have hS : mxSliceGate n k l = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun w hw =>
      h ⟨_, take_mem_mxHeadGate_of_mem_mxSliceGate hw⟩
  simp [hS, subMass_def, geomMass_empty]

open Classical in
/-- The submass of the gate union is at most the sum of `2^{-l}` over the indices `(k, l)`,
`k < n`, `l < 2n`, with nonempty head gate. -/
theorem subMass_mxGateUnion_le_sum (n : ℕ) (y : ResidueGroup n) :
    subMass n (mxGateUnion n) y ≤
      ∑ p ∈ (Finset.range n ×ˢ Finset.range (2 * n)).filter
        (fun p : ℕ × ℕ => (mxHeadGate n p.1 p.2).Nonempty), (2⁻¹ : ℝ≥0∞) ^ p.2 := by
  set s := Finset.range n ×ˢ Finset.range (2 * n)
  rw [mxGateUnion_eq_biUnion_product, subMass_biUnion_finset n s (pairwiseDisjoint_mxSliceGate n _),
    Finset.sum_filter]
  refine Finset.sum_le_sum fun p hp => ?_
  split_ifs with h
  · exact subMass_mxSliceGate_le_two_inv_pow (Finset.mem_range.1 (Finset.mem_product.1 hp).1) y
  · exact (subMass_mxSliceGate_eq_zero_of_not_nonempty h y).le

/-- The pointwise cap on the gate subdensity, for every `n ≥ 16`:
`g_n(y) ≤ (16/3) n^{5633/2048}`. -/
theorem mxSubdensity_le_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) (y : ResidueGroup n) :
    mxSubdensity n y ≤ 16 / 3 * (n : ℝ) ^ ((5633 : ℝ) / 2048) := by
  classical
  set t := (Finset.range n ×ˢ Finset.range (2 * n)).filter
    (fun p : ℕ × ℕ => (mxHeadGate n p.1 p.2).Nonempty)
  have hfin : ∑ p ∈ t, (2⁻¹ : ℝ≥0∞) ^ p.2 ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.pow_ne_top (by simp)
  have hreal : (subMass n (mxGateUnion n) y).toReal ≤ ∑ p ∈ t, (2⁻¹ : ℝ) ^ p.2 := by
    refine (ENNReal.toReal_mono hfin (subMass_mxGateUnion_le_sum n y)).trans_eq ?_
    rw [ENNReal.toReal_sum fun _ _ => ENNReal.pow_ne_top (by simp)]
    simp
  have hW := mxGateWeightSum_le_of_sixteen_le hn
  have hterm : ∀ p : ℕ × ℕ, (3 : ℝ) ^ n * (2 : ℝ) ^ (-(p.2 : ℤ)) = 3 ^ n * (2⁻¹ : ℝ) ^ p.2 :=
    fun p => by rw [zpow_neg, zpow_natCast, inv_pow]
  simp_rw [hterm, ← Finset.mul_sum] at hW
  rw [mxSubdensity_def]
  calc 2 / 3 * 3 ^ n * (subMass n (mxGateUnion n) y).toReal
      ≤ 2 / 3 * (3 ^ n * ∑ p ∈ t, (2⁻¹ : ℝ) ^ p.2) := by
        rw [mul_assoc]
        gcongr
    _ ≤ 2 / 3 * (8 * (n : ℝ) ^ ((5633 : ℝ) / 2048)) := by gcongr
    _ = 16 / 3 * (n : ℝ) ^ ((5633 : ℝ) / 2048) := by ring

/-- **Pointwise cap of the subdensity.** For every integer `n ≥ 2^131072` and `y ∈ G_n`,
`g_n(y) ≤ (16/3) n^{5633/2048}`. -/
@[collatz_pos_dens "lem_mx_subdensity_cap"]
theorem mxSubdensity_le_cap {n : ℕ} (hn : 2 ^ 131072 ≤ n) (y : ResidueGroup n) :
    mxSubdensity n y ≤ 16 / 3 * (n : ℝ) ^ ((5633 : ℝ) / 2048) := by
  have key : ∀ m, 4 ≤ m → 16 ≤ 2 ^ m := fun m hm => Nat.pow_le_pow_right (n := 2) Nat.two_pos hm
  exact mxSubdensity_le_of_sixteen_le ((key _ (by decide)).trans hn) y

end CollatzPosDens
