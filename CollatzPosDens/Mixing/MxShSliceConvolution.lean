/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxOffsetLaw
public import CollatzPosDens.Mixing.MxDyadicKernel
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxTailLaw
public import CollatzPosDens.Mixing.MxShClockOffset
public import CollatzPosDens.Mixing.MxShClockSum
public import CollatzPosDens.Mixing.MxShHeadMeasure
public import CollatzPosDens.Mixing.MxShSlice

/-!
# A slice is a convolution of a head measure and a tail law

Let `1 ≤ d ≤ n - 1`, `j ∈ ℕ` and `N = H^{sh}_n - 1`. The submass of the slice `Sl^{sh}_n(d, j)`
is the convolution of the head measure of the gate `(d, j)` with the tail law: for every
`x ∈ G_n`,
$$\mathrm{Sub}^n_{\mathrm{Sl}^{\mathrm{sh}}_n(d,j)}(x)
  = \sum_{y \in G_n} \Gamma^{\mathrm{sh}}_{n,d,j}(y)\,\mathrm{Tl}_{n,d-1,N}(x - y)
  \quad \text{in } [0, \infty].$$

Let `T = n - d` and `θ = [3^d 2^{-N}]_n`. For a tail `v` of length `T` with `z = [off(v)]_T`,
the dyadic rational `off(v) - z̃` is divisible by `3^T`, so `[3^d 2^{-N} off(v)]_n = θ z̃`. With
the binary-clock offset identity, a word `w` with `|Ex_N(w)| = d` has
`[off(w)]_n = [Of(Ex_N(w))]_n + θ · [off(Fr_N(w))]_T~`. The binary-clock law turns the submass
into `2^{-N} ∑_{β ∈ Hd^{sh}_n(d, j)} ∑_v 2^{-A(v)} [θ [off(v)]_T~ = x - [Of(β)]_n]`; grouping
the tails `v` by `z` and using the offset law of `μ_T` gives the tail law, and grouping the
patterns `β` by `[Of(β)]_n` gives the head measure. All terms are nonnegative, so the
rearrangements are justified in `[0, ∞]`.

## Main results

* `CollatzPosDens.subMass_mxShSlice_eq_sum`:
  `Sub^n_{Sl^sh_n(d,j)}(x) = ∑_y Γ^sh_{n,d,j}(y) Tl_{n,d-1,N}(x - y)`.

## Implementation notes

The head measure `Γ^{sh}_{n,d,j}` is rational-valued; it enters the identity in `[0, ∞]` through
`ENNReal.ofReal`. The clock position `N = H^{sh}_n - 1` uses truncated subtraction, which is
harmless since `H^{sh}_n ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

open Finset

/-- If `k + 1 + T = n`, then for every dyadic rational `q`,
`[3^{k+1} 2^{-l} q]_n = [3^{k+1} 2^{-l}]_n · ([q]_T)~`. -/
private theorem dyadicRed_mul_eq_tailLawCoeff_mul {n k l T : ℕ} (hT : k + 1 + T = n)
    (q : dyadicRationals) :
    dyadicRed n (⟨((3 ^ (k + 1) : ℤ) : ℚ) / 2 ^ l, intCast_div_two_pow_mem _ l⟩ * q) =
      tailLawCoeff n k l * ((dyadicRed T q).val : ResidueGroup n) := by
  set z := dyadicRed T q
  have hz : dyadicRed T (q - (z.val : dyadicRationals)) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨q', hq'⟩ := exists_eq_three_pow_mul_of_dyadicRed_eq_zero hz
  have hq : q = z.val + 3 ^ T * q' := by
    rw [← hq']
    ring
  have h3 : (3 : ResidueGroup n) ^ (k + 1) * 3 ^ T = 0 := by
    rw [← pow_add, hT]
    exact three_pow_self_residueGroup n
  rw [map_mul, ← tailLawCoeff, hq, map_add, map_natCast, map_mul, map_pow, map_ofNat, mul_add,
    tailLawCoeff_eq]
  have : (3 : ResidueGroup n) ^ (k + 1) * 2⁻¹ ^ l * (3 ^ T * dyadicRed n q') = 0 := by
    rw [show (3 : ResidueGroup n) ^ (k + 1) * 2⁻¹ ^ l * (3 ^ T * dyadicRed n q') =
      3 ^ (k + 1) * 3 ^ T * dyadicRed n q' * 2⁻¹ ^ l by ring, h3, zero_mul, zero_mul]
  rw [this, add_zero]

/-- The tails of length `n - k - 1`, translated by `y`, carry the tail law:
`∑_{v} 2^{-A(v)} [y + [3^{k+1} 2^{-l}]_n z̃(v) = x] = Tl_{n,k,l}(x - y)`. -/
private theorem tsum_tail_eq_tailLaw (n k l : ℕ) (x y : ResidueGroup n) :
    ∑' v : {v : Word // v.length = n - k - 1},
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
      ∑' v : {v : Word // v.length = n - k - 1},
        (if dyadicRed (n - k - 1) ⟨off v.1, off_mem_dyadicRationals v.1⟩ = z then
          (if tailLawCoeff n k l * (z.val : ResidueGroup n) = x - y then
            (2⁻¹ : ℝ≥0∞) ^ v.1.valSum else 0) else 0) := by
    intro z
    split_ifs
    · simp only [ENNReal.inv_pow]
      rfl
    · simp
  rw [Finset.sum_congr rfl fun z _ => hmove z,
    ← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine tsum_congr fun v => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, eq_sub_iff_add_eq']

/-- **A slice is a convolution of a head measure and a tail law.** Let `1 ≤ d ≤ n - 1` and
`j ∈ ℕ`, and write `N = H^{sh}_n - 1`. Then for every `x ∈ G_n`,
`Sub^n_{Sl^sh_n(d,j)}(x) = ∑_{y ∈ G_n} Γ^sh_{n,d,j}(y) Tl_{n,d-1,N}(x - y)` in `[0, ∞]`. -/
@[collatz_pos_dens "lem_mx_sh_slice_convolution"]
theorem subMass_mxShSlice_eq_sum {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d < n) (j : ℕ)
    (x : ResidueGroup n) :
    subMass n (mxShSlice n d j) x =
      ∑ y, ENNReal.ofReal (shHeadMeasure n d j y) * tailLaw n (d - 1) (shHeight n - 1) (x - y) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set N := shHeight n - 1 with hN
  set G := shRetainedHeads n (k + 1) j with hG
  let r : Finset ℕ → ResidueGroup n := fun β =>
    dyadicRed n ⟨setOffset β, setOffset_mem_dyadicRationals β⟩
  let F : Finset ℕ → Word → ℝ≥0∞ := fun β v =>
    if β ∈ G ∧ r β + tailLawCoeff n k N *
        ((dyadicRed (n - k - 1) ⟨off v, off_mem_dyadicRationals v⟩).val : ResidueGroup n) = x
      then 1 else 0
  have hstep : subMass n (mxShSlice n (k + 1) j) x =
      ∑' w : {w : Word // w.length = n ∧ #(Word.exposedPattern N w) = k + 1},
        (2⁻¹ : ℝ≥0∞) ^ Word.valSum w.1 * F (Word.exposedPattern N w.1) (Word.fresh N w.1) := by
    rw [subMass_eq_tsum, tsum_subtype (mxShSlice n (k + 1) j) (fun w : Word =>
        if dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ = x then (2⁻¹ : ℝ≥0∞) ^ w.valSum
        else 0)]
    refine Eq.trans ?_ (tsum_subtype {w : Word | w.length = n ∧
      #(Word.exposedPattern N w) = k + 1} (fun w : Word =>
        (2⁻¹ : ℝ≥0∞) ^ Word.valSum w * F (Word.exposedPattern N w) (Word.fresh N w))).symm
    refine tsum_congr fun w => ?_
    by_cases hw : w.length = n ∧ #(Word.exposedPattern N w) = k + 1
    · have hlt : #(Word.exposedPattern N w) < w.length := by omega
      have hred : dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ =
          r (Word.exposedPattern N w) + tailLawCoeff n k N *
            ((dyadicRed (n - k - 1) ⟨off (Word.fresh N w),
              off_mem_dyadicRationals _⟩).val : ResidueGroup n) := by
        have heq : (⟨off w, off_mem_dyadicRationals w⟩ : dyadicRationals) =
            ⟨setOffset (Word.exposedPattern N w), setOffset_mem_dyadicRationals _⟩ +
              ⟨((3 ^ (k + 1) : ℤ) : ℚ) / 2 ^ N, intCast_div_two_pow_mem _ N⟩ *
                ⟨off (Word.fresh N w), off_mem_dyadicRationals _⟩ := by
          apply Subtype.ext
          simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
          rw [Word.off_eq_setOffset_exposedPattern_add hlt, hw.2]
          push_cast
          ring
        rw [heq, map_add, dyadicRed_mul_eq_tailLawCoeff_mul (T := n - k - 1) (by omega)]
      have hmem : w ∈ mxShSlice n (k + 1) j ↔ Word.exposedPattern N w ∈ G :=
        ⟨fun h => h.2, fun h => ⟨hw.1, h⟩⟩
      rw [Set.indicator_of_mem (show w ∈ {w : Word | w.length = n ∧
        #(Word.exposedPattern N w) = k + 1} from hw)]
      simp only [Set.indicator, hmem, F, hred]
      by_cases hG' : Word.exposedPattern N w ∈ G <;> simp [hG']
    · have hnot : w ∉ mxShSlice n (k + 1) j := fun h =>
        hw ⟨h.1, card_exposedPattern_of_mem_mxShSlice h⟩
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem (show w ∉ {w : Word |
        w.length = n ∧ #(Word.exposedPattern N w) = k + 1} from hw)]
  rw [hstep, Word.tsum_exposedPattern_fresh N n (k + 1) hdn F]
  have hinner : ∀ β ∈ (Icc 1 N).powersetCard (k + 1),
      ∑' v : {v : Word // v.length = n - (k + 1)}, (2⁻¹ : ℝ≥0∞) ^ Word.valSum v.1 * F β v.1 =
        if β ∈ G then tailLaw n k N (x - r β) else 0 := by
    intro β _
    by_cases hβ : β ∈ G
    · simp only [hβ, ↓reduceIte]
      rw [← tsum_tail_eq_tailLaw n k N x (r β)]
      refine tsum_congr fun v => ?_
      simp only [F, hβ, true_and]
      split_ifs <;> simp
    · simp [F, hβ]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  have hfilter : ((Icc 1 N).powersetCard (k + 1)).filter (· ∈ G) = G := by
    ext β
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun h => shRetainedHeads_subset_powersetCard n (k + 1) j h
  rw [hfilter]
  have hΓ : ∀ y, ENNReal.ofReal (shHeadMeasure n (k + 1) j y) =
      (2⁻¹ : ℝ≥0∞) ^ N * (#{β ∈ G | r β = y} : ℝ≥0∞) := by
    intro y
    rw [shHeadMeasure_def]
    push_cast
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
      ENNReal.inv_pow]
  simp_rw [hΓ, mul_assoc, ← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_fiberwise G r (fun β => tailLaw n k N (x - r β))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl fun β hβ => by rw [(Finset.mem_filter.1 hβ).2], Finset.sum_const,
    nsmul_eq_mul]

end CollatzPosDens
