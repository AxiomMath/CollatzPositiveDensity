/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Case3.C3Anchors
public import CollatzPosDens.Case3.C3AnchorSep
public import CollatzPosDens.Case3.C3Big
public import CollatzPosDens.Case3.C3Eprime
public import CollatzPosDens.Case3.C3Near
public import CollatzPosDens.Case3.C3PackConst
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpPacking
public import CollatzPosDens.Renewal.RnListMarginal
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshMarginal
public import CollatzPosDens.Transfer.Qpack

/-!
# Mass of the large-triangle event outside the exceptional event

Let `e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗`, `G ∈ ℕ` with `l₀ + G = l_{Δ₀}` and `G ≥ 1024`, `v ∈ ℕ`, `X ≥ 1` an
integer and `s` a real number with `4096 X ≤ s` and `s² < 2G`, and assume
`2 G^{3/5} + 2 α X + 1 ≤ G δ₀`. Then
$$\mu_{e,G}(\mathrm{Big}_{e,G,v,s} \setminus \mathrm{Ex}_{e,G,v,X})
  < Q_{\mathrm{pack}}\,\frac Xs.$$

Let `𝒴 = Anc(Δ₀, s, 2X)` and `O = {o ∈ ℤ : -X < o < 2αX}`, so `0 ∈ O` and
`|O| = X - 1 + ⌈2αX⌉ < (1 + 2α) X` (`card_Ioo_neg_ceil_lt`). For `o ∈ O` the shifted set
`Z_o = 𝒴 - j₀ + o` is `d`-separated with `d = (36/25) α s` (`le_abs_sub_of_mem_image_bkAnchors`).
Every atom `a = ((r, ℓ), β)` of positive mass in `Big \ Ex` has `r ∈ ⋃_o Z_o`
(`exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional_epsStar`), so by
`tsum_trFreshLaw_mul_chBlockPoint` and the union bound the mass is at most
`∑_{o ∈ O} ∑_{r ∈ Z_o} ∑_ℓ F_G(r, ℓ)`, and `tsum_firstPassageLaw_packing_lt_ennreal` bounds each
inner sum by `17/(10√G) + 33/(32 d)`. Since `0 < s < √(2G)`, `1/√G < √2/s`, and the bound
`(1 + 2α)(17/10)√2 + (1/α + 2)(33/32)(25/36) < Q_pack` concludes.

## Main results

* `CollatzPosDens.tsum_trFreshLaw_c3Big_diff_c3Exceptional_lt`: the mass bound, as a sum
  in `[0, ∞]`.
* `CollatzPosDens.summable_trFreshLaw_c3Big_diff_c3Exceptional`: the fresh law is
  summable on the event.
* `CollatzPosDens.tsum_trFreshLaw_c3Big_diff_c3Exceptional_lt_real`: the mass bound, as a
  real sum.

## Implementation notes

The family is `𝔗 = 𝔗_{n,ξ,ε_*}` for a unit `ξ`. The mass `μ_{e,G}(·)` of an event is the
unconditional sum over the subtype of the event of `ENNReal.ofReal (trFreshLaw n e G a)`, which
needs no summability assumption; the real-valued form follows. The bound
`tsum_trFreshLaw_mul_chBlockPoint` is applied with no blocks, so no hypothesis `v ≤ J` is needed.
The integer `X ≥ 1` is taken in `ℤ`. The columns are summed over `r ∈ ℕ`, which embeds in `ℤ`, so
the vanishing of the columns `r ≤ 0` is not needed.

## References

* [Mazur, *Collatz positive density*], §10.3.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The column masses of `F_G` over the natural numbers `r` with `(r : ℤ) ∈ Z` are bounded by
the column masses over `Z`. -/
private lemma c3OutsideMass_cols_le (G : ℕ) (Z : Set ℤ) :
    ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((rl.1 : ℤ), rl.2)) *
        Z.indicator 1 (rl.1 : ℤ) ≤
      ∑' r : Z, ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw G ((r : ℤ), ℓ)) := by
  set g : ℤ → ℝ≥0∞ := fun r ↦ ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw G (r, ℓ)) with hg
  calc ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((rl.1 : ℤ), rl.2)) *
        Z.indicator 1 (rl.1 : ℤ)
      = ∑' r : ℕ, Z.indicator g (r : ℤ) := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun r ↦ ?_
        by_cases hr : (r : ℤ) ∈ Z
        · simp [Set.indicator_of_mem hr, hg]
        · simp [Set.indicator_of_notMem hr]
    _ ≤ ∑' z : ℤ, Z.indicator g z :=
        ENNReal.tsum_comp_le_tsum_of_injective Nat.cast_injective _
    _ = _ := (tsum_subtype Z g).symm

/-- The final numerical step: if `c < (1 + 2α) X`, `X ≥ 1`, `g > 0` and `0 < s < √2 g`, then
`c (17/(10 g) + 33/(32 · (36/25) α s)) ≤ Q_pack X / s`. -/
private lemma c3OutsideMass_numeric {c X s g : ℝ} (hc : c < (1 + 2 * alpha) * X)
    (hX : 1 ≤ X) (hs : 0 < s) (hg : 0 < g) (hsg : s < Real.sqrt 2 * g) :
    c * (17 / (10 * g) + 33 / (32 * (36 / 25 * alpha * s))) ≤ (Qpack : ℝ) * (X / s) := by
  have hα := alpha_pos
  have hP := packConst_lt_Qpack
  have hB0 : 0 < 17 / (10 * g) + 33 / (32 * (36 / 25 * alpha * s)) := by positivity
  have h1 : 17 / (10 * g) < 17 / 10 * Real.sqrt 2 / s := by
    rw [div_lt_div_iff₀ (by positivity) hs]
    nlinarith
  have hB : 17 / (10 * g) + 33 / (32 * (36 / 25 * alpha * s)) <
      ((1 + 2 * alpha) * (17 / 10) * Real.sqrt 2 + (1 / alpha + 2) * (33 / 32) * (25 / 36)) /
        ((1 + 2 * alpha) * s) := by
    have : ((1 + 2 * alpha) * (17 / 10) * Real.sqrt 2 + (1 / alpha + 2) * (33 / 32) * (25 / 36)) /
        ((1 + 2 * alpha) * s) = 17 / 10 * Real.sqrt 2 / s + 33 / (32 * (36 / 25 * alpha * s)) := by
      field_simp
    rw [this]
    linarith
  calc c * (17 / (10 * g) + 33 / (32 * (36 / 25 * alpha * s)))
      ≤ (1 + 2 * alpha) * X * (17 / (10 * g) + 33 / (32 * (36 / 25 * alpha * s))) :=
        mul_le_mul_of_nonneg_right hc.le hB0.le
    _ ≤ (1 + 2 * alpha) * X *
          (((1 + 2 * alpha) * (17 / 10) * Real.sqrt 2 + (1 / alpha + 2) * (33 / 32) * (25 / 36)) /
            ((1 + 2 * alpha) * s)) :=
        mul_le_mul_of_nonneg_left hB.le (by positivity)
    _ = ((1 + 2 * alpha) * (17 / 10) * Real.sqrt 2 + (1 / alpha + 2) * (33 / 32) * (25 / 36)) *
          (X / s) := by
        field_simp
    _ ≤ (Qpack : ℝ) * (X / s) :=
        mul_le_mul_of_nonneg_right hP.le (by positivity)

/-- Integer translates of the anchor set stay `(36/25) α s`-separated. -/
theorem le_abs_sub_of_mem_image_bkAnchors {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {Δ₀ : BkTriangle} {X : ℤ} (hX : 1 ≤ X) {s : ℝ} (hs : 4096 * X ≤ s) (j o : ℤ) :
    ∀ z ∈ (fun z ↦ z - j + o) '' bkAnchors (bkFamily n ξ epsStar) Δ₀ s (2 * X),
      ∀ z' ∈ (fun z ↦ z - j + o) '' bkAnchors (bkFamily n ξ epsStar) Δ₀ s (2 * X),
        z ≠ z' → 36 / 25 * alpha * s ≤ |(z : ℝ) - z'| := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hne
  have hα := alpha_pos
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hs0 : 0 < s := by linarith
  have hd0 : 0 < 36 / 25 * alpha * s := by positivity
  have hne' : y ≠ y' := fun h ↦ hne (by rw [h])
  have hdiff : ((y - j + o : ℤ) : ℝ) - ((y' - j + o : ℤ) : ℝ) = (y : ℝ) - y' := by
    push_cast
    ring
  rw [hdiff]
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · have := sub_gt_of_mem_bkAnchors hξ hX hs hy hy' hlt
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    exact this.le
  · have := sub_gt_of_mem_bkAnchors hξ hX hs hy' hy hlt
    rw [abs_of_pos (by linarith)]
    exact this.le

/-- The window `(-X, ⌈2 α X⌉)` has fewer than `(1 + 2α) X` integer points. -/
theorem card_Ioo_neg_ceil_lt {X : ℤ} (hX : 1 ≤ X) :
    ((Finset.Ioo (-X) ⌈2 * alpha * X⌉).card : ℝ) < (1 + 2 * alpha) * X := by
  have hα := alpha_pos
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hceil : (1 : ℤ) ≤ ⌈2 * alpha * X⌉ := by
    rw [Int.one_le_ceil_iff]
    positivity
  have hnn : 0 ≤ ⌈2 * alpha * (X : ℝ)⌉ - -X - 1 := by omega
  rw [Int.card_Ioo, ← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  push_cast
  have := Int.ceil_lt_add_one (2 * alpha * (X : ℝ))
  linarith

/-- For `X ≥ 1`, the window `(-X, ⌈2 α X⌉)` contains `0`. -/
theorem zero_mem_Ioo_neg_ceil {X : ℤ} (hX : 1 ≤ X) :
    (0 : ℤ) ∈ Finset.Ioo (-X) ⌈2 * alpha * X⌉ := by
  have hα := alpha_pos
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  rw [Finset.mem_Ioo, Int.lt_ceil]
  push_cast
  exact ⟨by omega, by positivity⟩

/-- Every atom of `Big_{e,G,v,s} \ Ex_{e,G,v,X}` of positive fresh mass lies in some translate
`Y - j₀ + o`, `o ∈ (-X, ⌈2 α X⌉)`, of the anchor set `Y`. -/
theorem one_le_sum_indicator_of_mem_c3Big_diff_c3Exceptional {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ}
    (he : e ∈ Δ₀) {G v : ℕ} (hG : bkL e + G = Δ₀.l) {X : ℤ} {s : ℝ}
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * X + 1 ≤ G * drift)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ c3Big n ξ epsStar e G v s \ c3Exceptional n e G v X)
    (hμ : trFreshLaw n e G a ≠ 0) :
    1 ≤ ∑ o ∈ Finset.Ioo (-X) ⌈2 * alpha * X⌉,
      ((fun z ↦ z - bkJ e + o) '' bkAnchors (bkFamily n ξ epsStar) Δ₀ s (2 * X)).indicator
        (1 : ℤ → ℝ≥0∞) (a.1.1 : ℤ) := by
  set Y := bkAnchors (bkFamily n ξ epsStar) Δ₀ s (2 * X) with hY
  set Z : ℤ → Set ℤ := fun o ↦ (fun z ↦ z - bkJ e + o) '' Y with hZ
  obtain ⟨z, hz, h1, h2⟩ :=
    exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional_epsStar hξ hΔ₀ he hG hGδ hμ
      ha.1 ha.2
  set o : ℤ := (a.1.1 : ℤ) + bkJ e - z with ho
  have hoO : o ∈ Finset.Ioo (-X) ⌈2 * alpha * X⌉ := by
    rw [Finset.mem_Ioo]
    constructor
    · have : (-X : ℝ) < (o : ℝ) := by
        rw [ho]
        push_cast
        linarith
      exact_mod_cast this
    · rw [Int.lt_ceil, ho]
      push_cast
      linarith
  have hmem : (a.1.1 : ℤ) ∈ Z o := ⟨z, hz, by rw [ho]; ring⟩
  calc (1 : ℝ≥0∞) = (Z o).indicator (1 : ℤ → ℝ≥0∞) (a.1.1 : ℤ) := by
        rw [Set.indicator_of_mem hmem]
        rfl
    _ ≤ _ := Finset.single_le_sum (f := fun o ↦ (Z o).indicator (1 : ℤ → ℝ≥0∞) (a.1.1 : ℤ))
        (fun _ _ ↦ zero_le) hoO

/-- A hold-list average over `Fin 0`-tuples is evaluation at the empty tuple. -/
theorem tsum_holdListLaw_fin_zero_mul (f : (Fin 0 → ℤ × ℤ) → ℝ≥0∞) :
    ∑' h : {h : Fin 0 → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) * f h.1 =
      f Fin.elim0 := by
  rw [tsum_eq_single ⟨Fin.elim0, fun i ↦ i.elim0⟩]
  · rw [holdListLaw_zero, ENNReal.ofReal_one, one_mul]
  · intro h hne
    exact absurd (Subtype.ext (funext fun i ↦ i.elim0)) hne

/-- **Mass of large triangles outside the exceptional event**. Let `ξ` be a unit,
`e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗 = 𝔗_{n,ξ,ε_*}`, `G ∈ ℕ` with `l₀ + G = l_{Δ₀}` and `G ≥ 1024`, `v ∈ ℕ`,
`X ≥ 1` an integer and `s` real with `4096 X ≤ s` and `s² < 2G`, and assume
`2 G^{3/5} + 2 α X + 1 ≤ G δ₀`. Then `μ_{e,G}(Big_{e,G,v,s} \ Ex_{e,G,v,X}) < Q_pack · X / s`. -/
@[collatz_pos_dens "lem_c3_outside_mass"]
theorem tsum_trFreshLaw_c3Big_diff_c3Exceptional_lt {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ}
    (he : e ∈ Δ₀) {G v : ℕ} (hG : bkL e + G = Δ₀.l) (hG1024 : 1024 ≤ G) {X : ℤ} (hX : 1 ≤ X)
    {s : ℝ} (hs : 4096 * X ≤ s) (hsG : s ^ 2 < 2 * G)
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * X + 1 ≤ G * drift) :
    ∑' a : ↥(c3Big n ξ epsStar e G v s \ c3Exceptional n e G v X),
        ENNReal.ofReal (trFreshLaw n e G a) <
      ENNReal.ofReal (Qpack * (X / s)) := by
  have hα := alpha_pos
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hs0 : 0 < s := by linarith
  set Y := bkAnchors (bkFamily n ξ epsStar) Δ₀ s (2 * X) with hY
  set O : Finset ℤ := Finset.Ioo (-X) ⌈2 * alpha * X⌉ with hO
  set Z : ℤ → Set ℤ := fun o ↦ (fun z ↦ z - bkJ e + o) '' Y with hZ
  set d : ℝ := 36 / 25 * alpha * s with hd
  have hd0 : 0 < d := by positivity
  set T : ℕ × ℤ → (Fin 0 → ℤ × ℤ) → ℝ≥0∞ := fun rl _ ↦
    ∑ o ∈ O, (Z o).indicator 1 (rl.1 : ℤ) with hT
  set B : ℝ := 17 / (10 * Real.sqrt G) + 33 / (32 * d) with hB
  have hsub : c3Big n ξ epsStar e G v s \ c3Exceptional n e G v X ⊆ trAtoms n :=
    Set.sdiff_subset.trans (c3Big_subset_trAtoms n ξ epsStar e G v s)
  set Φ : trAtoms n → ℝ≥0∞ := fun b ↦ ENNReal.ofReal (trFreshLaw n e G b) *
    T b.1.1 (fun i ↦ chBlockPoint (b.1.2[(i : ℕ)]'i.elim0)) with hΦ
  calc ∑' a : ↥(c3Big n ξ epsStar e G v s \ c3Exceptional n e G v X),
        ENNReal.ofReal (trFreshLaw n e G a)
      ≤ ∑' a : ↥(c3Big n ξ epsStar e G v s \ c3Exceptional n e G v X),
          Φ (Set.inclusion hsub a) := by
        refine ENNReal.tsum_le_tsum fun a ↦ ?_
        by_cases hμ : trFreshLaw n e G a = 0
        · simp [hμ]
        · calc ENNReal.ofReal (trFreshLaw n e G a) = ENNReal.ofReal (trFreshLaw n e G a) * 1 :=
                (mul_one _).symm
            _ ≤ _ := mul_le_mul_right
              (one_le_sum_indicator_of_mem_c3Big_diff_c3Exceptional hξ hΔ₀ he hG hGδ a.2 hμ) _
    _ ≤ ∑' b : trAtoms n, Φ b :=
        ENNReal.tsum_comp_le_tsum_of_injective (Set.inclusion_injective hsub) Φ
    _ = ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((rl.1 : ℤ), rl.2)) *
          ∑' h : {h : Fin 0 → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
            ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) * T rl h.1 :=
        tsum_trFreshLaw_mul_chBlockPoint n e G 0 (Nat.zero_le _) T
    _ = ∑' rl : ℕ × ℤ, ∑ o ∈ O, ENNReal.ofReal (firstPassageLaw G ((rl.1 : ℤ), rl.2)) *
          (Z o).indicator (1 : ℤ → ℝ≥0∞) (rl.1 : ℤ) := by
        refine tsum_congr fun rl ↦ ?_
        rw [← Finset.mul_sum]
        exact congrArg _ (tsum_holdListLaw_fin_zero_mul (T rl))
    _ = ∑ o ∈ O, ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((rl.1 : ℤ), rl.2)) *
          (Z o).indicator (1 : ℤ → ℝ≥0∞) (rl.1 : ℤ) :=
        Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable
    _ ≤ ∑ o ∈ O, ∑' r : Z o, ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw G ((r : ℤ), ℓ)) :=
        Finset.sum_le_sum fun o _ ↦ c3OutsideMass_cols_le G (Z o)
    _ < ∑ _o ∈ O, ENNReal.ofReal B :=
        ENNReal.sum_lt_sum_of_nonempty ⟨0, zero_mem_Ioo_neg_ceil hX⟩ fun o _ ↦
          tsum_firstPassageLaw_packing_lt_ennreal hG1024 hd0 (Z o)
            (le_abs_sub_of_mem_image_bkAnchors hξ hX hs (bkJ e) o)
    _ = ENNReal.ofReal (O.card * B) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (Qpack * (X / s)) :=
        ENNReal.ofReal_le_ofReal <| c3OutsideMass_numeric (card_Ioo_neg_ceil_lt hX) hXr hs0
          (Real.sqrt_pos.2 (by positivity)) <| by
            rw [← Real.sqrt_mul (by norm_num)]
            exact Real.lt_sqrt_of_sq_lt hsG

/-- The fresh law is summable on `Big_{e,G,v,s} \ Ex_{e,G,v,X}`, under the hypotheses of
`tsum_trFreshLaw_c3Big_diff_c3Exceptional_lt`. -/
theorem summable_trFreshLaw_c3Big_diff_c3Exceptional {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ}
    (he : e ∈ Δ₀) {G v : ℕ} (hG : bkL e + G = Δ₀.l) (hG1024 : 1024 ≤ G) {X : ℤ} (hX : 1 ≤ X)
    {s : ℝ} (hs : 4096 * X ≤ s) (hsG : s ^ 2 < 2 * G)
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * X + 1 ≤ G * drift) :
    Summable fun a : ↥(c3Big n ξ epsStar e G v s \ c3Exceptional n e G v X) ↦
      trFreshLaw n e G a :=
  summable_trFreshLaw_of_tsum_ofReal_ne_top
    ((tsum_trFreshLaw_c3Big_diff_c3Exceptional_lt (v := v) hξ hΔ₀ he hG hG1024 hX hs hsG
      hGδ).trans ENNReal.ofReal_lt_top).ne

/-- **Mass of large triangles outside the exceptional event**, as a real sum:
`μ_{e,G}(Big_{e,G,v,s} \ Ex_{e,G,v,X}) < Q_pack · X / s`. -/
theorem tsum_trFreshLaw_c3Big_diff_c3Exceptional_lt_real {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ}
    (he : e ∈ Δ₀) {G v : ℕ} (hG : bkL e + G = Δ₀.l) (hG1024 : 1024 ≤ G) {X : ℤ} (hX : 1 ≤ X)
    {s : ℝ} (hs : 4096 * X ≤ s) (hsG : s ^ 2 < 2 * G)
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * X + 1 ≤ G * drift) :
    ∑' a : ↥(c3Big n ξ epsStar e G v s \ c3Exceptional n e G v X), trFreshLaw n e G a <
      Qpack * (X / s) := by
  have h := tsum_trFreshLaw_c3Big_diff_c3Exceptional_lt (v := v) hξ hΔ₀ he hG hG1024 hX hs hsG hGδ
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _)
    (summable_trFreshLaw_c3Big_diff_c3Exceptional (v := v) hξ hΔ₀ he hG hG1024 hX hs hsG
      hGδ)] at h
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (tsum_nonneg fun _ ↦ trFreshLaw_nonneg _ _ _ _)).1 h

end CollatzPosDens
