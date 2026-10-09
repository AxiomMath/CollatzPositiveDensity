/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxOffsetLaw
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Mixing.MxDyadicKernel
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxTailLaw
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxHeadMass
public import CollatzPosDens.Mixing.MxSliceGate

/-!
# Slices as convolutions

Let `k < n` and `T = n - k - 1`. The submass of the slice gate `Sl(n, k, l)` is the convolution
of the head mass with the tail law: for every `x ∈ G_n`,
$$\mathrm{Sub}^n_{\mathrm{Sl}(n,k,l)}(x)
  = \sum_{y \in G_n} \mathrm{Hm}_{n,k,l}(y)\,\mathrm{Tl}_{n,k,l}(x - y).$$

Splitting `w = hv` with `|h| = k + 1` and `|v| = T` is a bijection from `Sl(n, k, l)` onto
`Hd(n, k, l) × ℤ_{≥1}^T`, with `A(w) = l + A(v)` and `off(w) = off(h) + 3^{k+1} 2^{-l} off(v)`.
Writing `z = [off(v)]_T`, the dyadic rational `off(v) - z̃` is divisible by `3^T` in `ℤ[1/2]`,
so `[off(w)]_n = [off(h)]_n + [3^{k+1} 2^{-l}]_n z̃`. Grouping the tails `v` by `z` and using
the offset law of `μ_T` gives the tail law, and grouping the heads `h` by `[off(h)]_n` gives the
head mass.

## Main results

* `CollatzPosDens.subMass_mxSliceGate_eq_sum`: `Sub^n_{Sl(n,k,l)}(x) = ∑_y Hm(y) Tl(x - y)`.

## Implementation notes

The head mass is real-valued and the tail law and the submass take values in `[0, ∞]`, so the
identity is stated in `ℝ≥0∞` with the head mass read through `ENNReal.ofReal`. The hypothesis
`n ≥ 1` follows from `k < n` and is not stated separately.

## References

* [Mazur, *Collatz positive density*, §13.7]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For `h ∈ Hd(n, k, l)` and `k < n`,
`[off(hv)]_n = [off(h)]_n + [3^{k+1} 2^{-l}]_n · z̃` with `z = [off(v)]_{n-k-1}`. -/
private theorem dyadicRed_off_append_of_mem_mxHeadGate {n k l : ℕ} (hk : k < n) {h : Word}
    (hh : h ∈ mxHeadGate n k l) (v : Word) :
    dyadicRed n ⟨off (h ++ v), off_mem_dyadicRationals _⟩ =
      dyadicRed n ⟨off h, off_mem_dyadicRationals h⟩ + tailLawCoeff n k l *
        ((dyadicRed (n - k - 1) ⟨off v, off_mem_dyadicRationals v⟩).val : ResidueGroup n) := by
  set T := n - k - 1
  set z := dyadicRed T ⟨off v, off_mem_dyadicRationals v⟩
  have hz : dyadicRed T (⟨off v, off_mem_dyadicRationals v⟩ - (z.val : dyadicRationals)) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨q, hq⟩ := exists_eq_three_pow_mul_of_dyadicRed_eq_zero hz
  have hv : (⟨off v, off_mem_dyadicRationals v⟩ : dyadicRationals) = z.val + 3 ^ T * q := by
    rw [← hq]; ring
  have hlen : h.length = k + 1 := length_of_mem_mxHeadGate hh
  have hval : h.valSum = l := valSum_of_mem_mxHeadGate hh
  have hw : dyadicRed n ⟨h.weight, h.weight_mem_dyadicRationals⟩ = tailLawCoeff n k l := by
    rw [dyadicRed_weight, tailLawCoeff_eq, hlen, hval]
  have h3 : (3 : ResidueGroup n) ^ (k + 1) * 3 ^ T = 0 := by
    rw [← pow_add, show k + 1 + T = n by omega]
    exact three_pow_self_residueGroup n
  rw [dyadicRed_off_append, hw, hv, map_add, map_mul, map_natCast, map_pow, map_ofNat,
    mul_add, tailLawCoeff_eq]
  have : (3 : ResidueGroup n) ^ (k + 1) * 2⁻¹ ^ l * 3 ^ T * dyadicRed n q = 0 := by
    rw [mul_right_comm _ _ ((3 : ResidueGroup n) ^ T), h3, zero_mul, zero_mul]
  rw [← mul_assoc _ ((3 : ResidueGroup n) ^ T), this, add_zero]

/-- The tails of length `n - k - 1`, translated by `y`, carry the tail law:
`∑_{v} 2^{-A(v)} [y + [3^{k+1} 2^{-l}]_n z̃(v) = x] = Tl_{n,k,l}(x - y)`. -/
private theorem tsum_tail_eq_tailLaw (n k l : ℕ) (x y : ResidueGroup n) :
    ∑' v : {v : Word | v.length = n - k - 1},
      (if y + tailLawCoeff n k l *
          ((dyadicRed (n - k - 1) ⟨off v.1, off_mem_dyadicRationals v.1⟩).val : ResidueGroup n) = x
        then (2⁻¹ : ℝ≥0∞) ^ v.1.valSum else 0) = tailLaw n k l (x - y) := by
  rw [tailLaw_eq_sum_ite]
  simp_rw [refLaw_eq_tsum_off]
  have hmove : ∀ z : ResidueGroup (n - k - 1),
      (if tailLawCoeff n k l * (z.val : ResidueGroup n) = x - y then
        ∑' v : {v : Word | v.length = n - k - 1},
          (if dyadicRed (n - k - 1) ⟨off v.1, off_mem_dyadicRationals v.1⟩ = z then
            ((2 : ℝ≥0∞) ^ v.1.valSum)⁻¹ else 0) else 0) =
      ∑' v : {v : Word | v.length = n - k - 1},
        (if dyadicRed (n - k - 1) ⟨off v.1, off_mem_dyadicRationals v.1⟩ = z then
          (if tailLawCoeff n k l * (z.val : ResidueGroup n) = x - y then
            (2⁻¹ : ℝ≥0∞) ^ v.1.valSum else 0) else 0) := by
    intro z
    split_ifs <;> simp [ENNReal.inv_pow]
  rw [Finset.sum_congr rfl fun z _ => hmove z,
    ← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine tsum_congr fun v => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, eq_sub_iff_add_eq']

/-- **Slices as convolutions.** For `k < n` and `x ∈ G_n`,
`Sub^n_{Sl(n,k,l)}(x) = ∑_{y ∈ G_n} Hm_{n,k,l}(y) Tl_{n,k,l}(x - y)`. -/
@[collatz_pos_dens "lem_mx_slice_convolution"]
theorem subMass_mxSliceGate_eq_sum {n k l : ℕ} (hk : k < n) (x : ResidueGroup n) :
    subMass n (mxSliceGate n k l) x =
      ∑ y, ENNReal.ofReal (mxHeadMass n k l y) * tailLaw n k l (x - y) := by
  set F := (mxHeadGate_finite n k l).toFinset
  let r : Word → ResidueGroup n := fun h => dyadicRed n ⟨off h, off_mem_dyadicRationals h⟩
  have hF : ∀ h, h ∈ F ↔ h ∈ mxHeadGate n k l := fun h => Set.Finite.mem_toFinset _
  let e : F × {v : Word | v.length = n - k - 1} ≃ mxSliceGate n k l :=
    { toFun := fun p => ⟨p.1.1 ++ p.2.1, by
        have h1 := (hF _).1 p.1.2
        refine ⟨?_, ?_⟩
        · rw [List.length_append, h1.1, p.2.2]; omega
        · rw [List.take_left' h1.1]; exact h1⟩
      invFun := fun w => (⟨w.1.take (k + 1), (hF _).2 w.2.2⟩,
        ⟨w.1.drop (k + 1), by simp [w.2.1]; omega⟩)
      left_inv := fun p => by
        have h1 := ((hF _).1 p.1.2).1
        ext
        · simp [List.take_left' h1]
        · simp [List.drop_left' h1]
      right_inv := fun w => Subtype.ext (List.take_append_drop _ _) }
  have hsum : subMass n (mxSliceGate n k l) x =
      ∑' p : F × {v : Word | v.length = n - k - 1}, (2⁻¹ : ℝ≥0∞) ^ l *
        (if r p.1.1 + tailLawCoeff n k l *
            ((dyadicRed (n - k - 1) ⟨off p.2.1, off_mem_dyadicRationals p.2.1⟩).val :
              ResidueGroup n) = x
          then (2⁻¹ : ℝ≥0∞) ^ p.2.1.valSum else 0) := by
    rw [subMass_eq_tsum, ← e.tsum_eq]
    refine tsum_congr fun p => ?_
    have h1 := (hF _).1 p.1.2
    change (if dyadicRed n ⟨off (p.1.1 ++ p.2.1), _⟩ = x then
      (2⁻¹ : ℝ≥0∞) ^ (p.1.1 ++ p.2.1).valSum else 0) = _
    rw [dyadicRed_off_append_of_mem_mxHeadGate hk h1, Word.valSum_append,
      valSum_of_mem_mxHeadGate h1, pow_add]
    split_ifs <;> simp
  rw [hsum, ENNReal.tsum_prod (f := fun (h : F) (v : {v : Word | v.length = n - k - 1}) =>
    (2⁻¹ : ℝ≥0∞) ^ l * (if r h.1 + tailLawCoeff n k l *
      ((dyadicRed (n - k - 1) ⟨off v.1, off_mem_dyadicRationals v.1⟩).val : ResidueGroup n) = x
        then (2⁻¹ : ℝ≥0∞) ^ v.1.valSum else 0))]
  refine (tsum_congr fun a => ?_ :
    _ = ∑' a : F, (2⁻¹ : ℝ≥0∞) ^ l * tailLaw n k l (x - r a.1)).trans ?_
  · rw [ENNReal.tsum_mul_left, tsum_tail_eq_tailLaw]
  rw [Finset.tsum_subtype F (fun h => (2⁻¹ : ℝ≥0∞) ^ l * tailLaw n k l (x - r h)),
    ← Finset.sum_fiberwise F r]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mxHeadMass_def, ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_filter] at hh
  have hval : h.valSum = l := valSum_of_mem_mxHeadGate ((hF _).1 hh.1)
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num), hval]
  change _ = _ * tailLaw n k l (x - y)
  rw [← hh.2]
  simp [r]

end CollatzPosDens
