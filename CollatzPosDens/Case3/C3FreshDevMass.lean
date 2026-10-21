/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3AffineBarrier
public import CollatzPosDens.Case3.C3FreshDev
public import CollatzPosDens.Case3.C3GfDrift
public import CollatzPosDens.Case3.C3GfVert
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.StoppingTrace.TrFreshMarginal
public import CollatzPosDens.Transfer.S02UdLem
public import CollatzPosDens.Transfer.S02UvLem

/-!
# Mass of the common fresh deviation event

Let `ι ∈ 𝔍` be a Fourier index, `e ∈ 𝒫` and `g ∈ ℕ`. The common fresh deviation event has
fresh-law mass `μ_{e,g}(Dev^fr(ι)) ≤ U_v(ι) + U_d(ι)`.

Put `N₀ = min(V_*(ι) - 1, ⌊n/2⌋)`. Membership of an atom `((r, ℓ), β)` in `Dev^fr(ι)` depends
only on the block points `h = (bpt(β¹), …, bpt(β^{N₀}))`, through the partial sums
`h₁ + ⋯ + h_u`. By the displacement marginal of the fresh law and the total mass `1` of `F_g`, the
mass of `Dev^fr(ι)` is at most the `η^{⊗N₀}`-mass of `E_l ∪ E_+ ∪ E_-`, where `E_l` is the event
`l(h₁ + ⋯ + h_u) ≥ X_l(ι, u)` and `E_ς` the event `ς (4j - l)(h₁ + ⋯ + h_u) ≥ 4 X_d(ι, u)`, each
for some `1 ≤ u ≤ N₀`.

* *Vertical.* With `y = y_dv(ι) > 1` (`169/168` or `144/143`), `η = η_dv(ι)` and
  `X_l(ι, u) = X_l(ι, 0) + η u`, the condition defining `E_l` at `u` implies
  `y^{l(h₁ + ⋯ + h_u)} ≥ y^{X_l(ι, 0)} (y^η)^u`. The affine barrier with `X = 1`,
  `T = y^{X_l(ι, 0)}` and `Λ = y^η ≥ 𝖦(1, y)` bounds the mass of `E_l` by
  `y^{-X_l(ι, 0)} ≤ U_v(ι)`.
* *Drift-free.* With `b = b_dv(ι) > 1` (`51/50` or `43/42`), `σ = σ_dv(ι)` and
  `4 X_d(ι, u) = 4 X_d(ι, 0) + σ u`, the condition defining `E_ς` at `u` implies
  `(b^{4ς})^j (b^{-ς})^l ≥ b^{4 X_d(ι, 0)} (b^σ)^u` at `h₁ + ⋯ + h_u`. The affine barrier with
  `X = b^{4ς}`, `y = b^{-ς}`, `T = b^{4 X_d(ι, 0)}` and `Λ = b^σ` bounds the mass of `E_ς` by
  `b^{-4 X_d(ι, 0)}`, and `2 b^{-4 X_d(ι, 0)} ≤ U_d(ι)`.

The union bound finishes the proof.

## Main results

* `CollatzPosDens.tsum_trFreshLaw_c3FreshDev_le`: `μ_{e,g}(Dev^fr(ι)) ≤ U_v(ι) + U_d(ι)`, as a
  sum in `[0, ∞]`.
* `CollatzPosDens.summable_trFreshLaw_c3FreshDev`: the fresh law is summable on `Dev^fr(ι)`.
* `CollatzPosDens.tsum_trFreshLaw_c3FreshDev_le_real`: `μ_{e,g}(Dev^fr(ι)) ≤ U_v(ι) + U_d(ι)`, as
  a real sum.

## Implementation notes

The mass `μ_{e,g}(Dev^fr(ι))` is the unconditional sum over the subtype `Dev^fr(ι)` of
`ENNReal.ofReal (trFreshLaw n e g a)`; this form makes no summability assumption, and the real
form follows. The equality `μ_{e,g}(Dev^fr(ι)) = η^{⊗N₀}(E_l ∪ E_+ ∪ E_-)` holds when `F_g` has
total mass `1`; only the inequality `≤` is proved, and it holds without that assumption. The
hypothesis `e ∈ 𝒫` plays no role and is dropped; the statement holds for every level `n`.

## References

* [Mazur, *Collatz positive density*], §10.5.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The sum over the first `u` entries of a list, as a sum over the `i : Fin v` with `i < u`. -/
private lemma c3FreshDevMass_sum_take {α M : Type*} [AddCommMonoid M] (f : α → M)
    (β : List α) {u v : ℕ} (huv : u ≤ v) (hv : v ≤ β.length) :
    ((β.take u).map f).sum =
      ∑ i : Fin v with i.val < u, f (β[(i : ℕ)]'(lt_of_lt_of_le i.2 hv)) := by
  have h : β.take u = List.ofFn fun i : Fin u ↦ β[(i : ℕ)]'(by omega) := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp
  rw [h, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_bij (fun i _ ↦ Fin.castLE huv i) (fun i _ ↦ by simp)
    (fun i _ j _ hij ↦ Fin.castLE_injective huv hij) (fun j hj ↦ ?_) (fun i _ ↦ rfl)
  simp only [Finset.mem_filter] at hj
  exact ⟨⟨j, hj.2⟩, Finset.mem_univ _, rfl⟩

/-- On a tuple of points of `𝒫`, the `j`-coordinates read in `ℕ` sum to the `j`-coordinate of the
sum. -/
private lemma c3FreshDevMass_cast_sum_toNat {v : ℕ} (h : Fin v → ℤ × ℤ)
    (hh : ∀ i, h i ∈ bkPoints) (s : Finset (Fin v)) :
    ((∑ i ∈ s, (h i).1.toNat : ℕ) : ℤ) = ∑ i ∈ s, (h i).1 := by
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ Int.toNat_of_nonneg ?_
  have := mem_bkPoints.1 (hh i)
  simp only [bkJ] at this
  omega

/-- The vertical event `E_l`: `l(h₁ + ⋯ + h_u) ≥ X_l(ι, u)` for some `1 ≤ u ≤ v`. -/
private def c3FreshDevVert (ι : FIndex) (v : ℕ) : Set (Fin v → ℤ × ℤ) :=
  {h | ∃ u ∈ Finset.Icc 1 v, Xl ι u ≤ ((∑ i : Fin v with i.val < u, h i).2 : ℚ)}

/-- The drift-free event `E_ς`: `ς (4j - l)(h₁ + ⋯ + h_u) ≥ 4 X_d(ι, u)` for some
`1 ≤ u ≤ v`. -/
private def c3FreshDevDrift (ι : FIndex) (v : ℕ) (ς : ℤ) : Set (Fin v → ℤ × ℤ) :=
  {h | ∃ u ∈ Finset.Icc 1 v, 4 * Xd ι u ≤
    ((ς * (4 * (∑ i : Fin v with i.val < u, h i).1 - (∑ i : Fin v with i.val < u, h i).2) : ℤ) :
      ℚ)}

/-- The vertical event has `η^{⊗v}`-mass at most `y_dv(ι)^{-X_l(ι, 0)}`. -/
private lemma c3FreshDevMass_vert (ι : FIndex) (v : ℕ) :
    ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
          {h | h ∈ c3FreshDevVert ι v}.indicator 1 h.1 ≤
      ENNReal.ofReal ((devY ι : ℝ) ^ (-(Xl ι 0 : ℝ))) := by
  have hy : (0 : ℝ) < devY ι := by exact_mod_cast devY_pos ι
  have hy1 : (1 : ℝ) ≤ devY ι := by exact_mod_cast (one_lt_devY ι).le
  have hT : 0 < (devY ι : ℝ) ^ (Xl ι 0 : ℝ) := Real.rpow_pos_of_pos hy _
  refine (tsum_holdListLaw_bkPoints_mul_indicator_le (fun h ↦ h ∈ c3FreshDevVert ι v)
    (fun w ↦ ∃ u ∈ Finset.Icc 1 v,
      (devY ι : ℝ) ^ (Xl ι 0 : ℝ) * ((devY ι : ℝ) ^ (devEta ι : ℝ)) ^ u ≤
      (1 : ℝ) ^ (∑ i : Fin v with i.val < u, (w i).1) *
        (devY ι : ℝ) ^ (∑ i : Fin v with i.val < u, (w i).2)) ?_).trans
    ((tsum_ofReal_holdListLaw_affine_barrier one_pos hy v hT
      (holdJointPgf_one_devY_lt ι).le).trans (le_of_eq ?_))
  · rintro h - ⟨u, hu, hle⟩
    refine ⟨u, hu, ?_⟩
    rw [one_pow, one_mul, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_add hy,
      ← Real.rpow_intCast]
    refine Real.rpow_le_rpow_of_exponent_le hy1 ?_
    rw [Xl_eq_Xl_zero_add] at hle
    have hle' := (Rat.cast_le (K := ℝ)).2 hle
    rw [Prod.snd_sum] at hle'
    push_cast at hle' ⊢
    linarith
  · rw [one_div, Real.rpow_neg hy.le]

/-- The drift-free event `E_ς` has `η^{⊗v}`-mass at most `b_dv(ι)^{-4 X_d(ι, 0)}`. -/
private lemma c3FreshDevMass_drift (ι : FIndex) (v : ℕ) {ς : ℤ} (hς : ς = 1 ∨ ς = -1) :
    ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
          {h | h ∈ c3FreshDevDrift ι v ς}.indicator 1 h.1 ≤
      ENNReal.ofReal ((devB ι : ℝ) ^ (-(4 * (Xd ι 0 : ℝ)))) := by
  have hb : (0 : ℝ) < devB ι := by exact_mod_cast devB_pos ι
  have hb1 : (1 : ℝ) ≤ devB ι := by exact_mod_cast (one_lt_devB ι).le
  have hT : 0 < (devB ι : ℝ) ^ (4 * (Xd ι 0 : ℝ)) := Real.rpow_pos_of_pos hb _
  refine (tsum_holdListLaw_bkPoints_mul_indicator_le (fun h ↦ h ∈ c3FreshDevDrift ι v ς)
    (fun w ↦ ∃ u ∈ Finset.Icc 1 v,
      (devB ι : ℝ) ^ (4 * (Xd ι 0 : ℝ)) * ((devB ι : ℝ) ^ (devSigma ι : ℝ)) ^ u ≤
        ((devB ι : ℝ) ^ (4 * ς)) ^ (∑ i : Fin v with i.val < u, (w i).1) *
          ((devB ι : ℝ) ^ (-ς)) ^ (∑ i : Fin v with i.val < u, (w i).2)) ?_).trans
    ((tsum_ofReal_holdListLaw_affine_barrier (zpow_pos hb _) (zpow_pos hb _) v hT
      (holdJointPgf_devB_lt ι hς).le).trans (le_of_eq ?_))
  · rintro h hh ⟨u, hu, hle⟩
    refine ⟨u, hu, ?_⟩
    rw [← zpow_natCast ((devB ι : ℝ) ^ (4 * ς)), ← zpow_mul, ← zpow_mul, ← zpow_add₀ hb.ne',
      ← Real.rpow_natCast ((devB ι : ℝ) ^ (devSigma ι : ℝ)), ← Real.rpow_mul hb.le,
      ← Real.rpow_add hb, ← Real.rpow_intCast]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have hJ := c3FreshDevMass_cast_sum_toNat h hh {i : Fin v | i.val < u}
    rw [Xd_eq_Xd_zero_add] at hle
    have hle' := (Rat.cast_le (K := ℝ)).2 hle
    rw [Prod.snd_sum, Prod.fst_sum] at hle'
    rw [hJ]
    push_cast at hle' ⊢
    linarith
  · rw [one_div, Real.rpow_neg hb.le]

/-- If `T` is at least `1` on an event `S ⊆ 𝒜_n`, the fresh-law mass of `S` is bounded by the
integral of `T` against the displacement marginal. -/
private lemma c3FreshDevMass_le_of_one_le {n : ℕ} (e : ℤ × ℤ) (g : ℕ) {v : ℕ} (hv : v ≤ n / 2)
    {S : Set ((ℕ × ℤ) × List (List ℤ × ℤ))} (hS : S ⊆ trAtoms n)
    (T : (Fin v → ℤ × ℤ) → ℝ≥0∞)
    (hT : ∀ a ∈ S, (ha : a ∈ trAtoms n) → 1 ≤ T (fun i : Fin v ↦ chBlockPoint (a.2[(i : ℕ)]'(by
      have := (mem_trAtoms.1 ha).1; omega)))) :
    ∑' a : S, ENNReal.ofReal (trFreshLaw n e g a) ≤
      ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) *
        ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
          ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) * T h.1 := by
  rw [← tsum_trFreshLaw_mul_chBlockPoint n e g v hv (fun _ ↦ T)]
  calc _ ≤ ∑' a : S, (fun b : trAtoms n ↦ ENNReal.ofReal (trFreshLaw n e g b) *
          T (fun i ↦ chBlockPoint (b.1.2[(i : ℕ)]'(by
            have := (mem_trAtoms.1 b.2).1; omega)))) (Set.inclusion hS a) :=
        ENNReal.tsum_le_tsum fun a ↦ le_mul_of_one_le_right' (hT a.1 a.2 (hS a.2))
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (Set.inclusion_injective hS)
        (fun b : trAtoms n ↦ ENNReal.ofReal (trFreshLaw n e g b) *
          T (fun i ↦ chBlockPoint (b.1.2[(i : ℕ)]'(by
            have := (mem_trAtoms.1 b.2).1; omega))))

/-- **Mass of the common fresh deviation event**, in `[0, ∞]`:
`μ_{e,g}(Dev^fr(ι)) ≤ U_v(ι) + U_d(ι)`. -/
@[collatz_pos_dens "lem_c3_fresh_dev_mass"]
theorem tsum_trFreshLaw_c3FreshDev_le (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (g : ℕ) :
    ∑' a : c3FreshDev ι n, ENNReal.ofReal (trFreshLaw n e g a) ≤
      ENNReal.ofReal ((Uv ι : ℝ) + Ud ι) := by
  set v := min (Vstar ι - 1) (n / 2) with hvdef
  have hv : v ≤ n / 2 := min_le_right _ _
  set T : (Fin v → ℤ × ℤ) → ℝ≥0∞ := fun h ↦ {h | h ∈ c3FreshDevVert ι v}.indicator 1 h +
    ({h | h ∈ c3FreshDevDrift ι v 1}.indicator 1 h +
      {h | h ∈ c3FreshDevDrift ι v (-1)}.indicator 1 h) with hTdef
  have hcover : ∀ a ∈ c3FreshDev ι n, (ha : a ∈ trAtoms n) →
      1 ≤ T (fun i : Fin v ↦ chBlockPoint (a.2[(i : ℕ)]'(by
          have := (mem_trAtoms.1 ha).1; omega))) := by
    intro a hdev ha
    have hlen : v ≤ a.2.length := by rw [(mem_trAtoms.1 ha).1]; exact hv
    obtain ⟨-, u, hu1, huv, hu⟩ := mem_c3FreshDev_iff_blockPoint_sum.1 hdev
    have huI : u ∈ Finset.Icc 1 v := Finset.mem_Icc.2 ⟨hu1, huv⟩
    rw [c3FreshDevMass_sum_take chBlockPoint a.2 huv hlen] at hu
    rcases hu with hl | hd
    · have hmem : (fun i : Fin v ↦ chBlockPoint (a.2[(i : ℕ)]'(lt_of_lt_of_le i.2 hlen))) ∈
          {h | h ∈ c3FreshDevVert ι v} := ⟨u, huI, hl⟩
      exact le_add_right (Set.indicator_of_mem hmem 1).ge
    · rcases le_abs'.1 hd with hneg | hpos
      · have hmem : (fun i : Fin v ↦ chBlockPoint (a.2[(i : ℕ)]'(lt_of_lt_of_le i.2 hlen))) ∈
            {h | h ∈ c3FreshDevDrift ι v (-1)} := by
          refine ⟨u, huI, ?_⟩
          push_cast at hneg ⊢
          linarith
        exact le_add_left (le_add_left (Set.indicator_of_mem hmem 1).ge)
      · have hmem : (fun i : Fin v ↦ chBlockPoint (a.2[(i : ℕ)]'(lt_of_lt_of_le i.2 hlen))) ∈
            {h | h ∈ c3FreshDevDrift ι v 1} := by
          refine ⟨u, huI, ?_⟩
          push_cast at hpos ⊢
          linarith
        exact le_add_left (le_add_right (Set.indicator_of_mem hmem 1).ge)
  set η : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints} → ℝ≥0∞ :=
    fun h ↦ ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) with hηdef
  set dY : ℝ := (devY ι : ℝ) ^ (-(Xl ι 0 : ℝ))
  set dB : ℝ := (devB ι : ℝ) ^ (-(4 * (Xd ι 0 : ℝ)))
  have hdB : 0 ≤ dB := Real.rpow_nonneg (by exact_mod_cast devB_nonneg ι) _
  have hdY : 0 ≤ dY := Real.rpow_nonneg (by exact_mod_cast devY_nonneg ι) _
  have hinner : ∑' h, η h * T h.1 ≤
      ENNReal.ofReal dY + (ENNReal.ofReal dB + ENNReal.ofReal dB) := by
    simp only [hTdef, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_add]
    exact add_le_add (c3FreshDevMass_vert ι v)
      (add_le_add (c3FreshDevMass_drift ι v (Or.inl rfl))
        (c3FreshDevMass_drift ι v (Or.inr rfl)))
  have hfinal : ENNReal.ofReal dY + (ENNReal.ofReal dB + ENNReal.ofReal dB) ≤
      ENNReal.ofReal ((Uv ι : ℝ) + Ud ι) := by
    rw [← ENNReal.ofReal_add hdB hdB, ← ENNReal.ofReal_add hdY (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hY : dY ≤ Uv ι := devY_rpow_neg_Xl_zero_le_Uv ι
    have hB : 2 * dB ≤ Ud ι := Ud_bound ι
    linarith
  calc _ ≤ _ := c3FreshDevMass_le_of_one_le e g hv (c3FreshDev_subset_trAtoms ι n) T hcover
    _ ≤ ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) *
          (ENNReal.ofReal dY + (ENNReal.ofReal dB + ENNReal.ofReal dB)) :=
        ENNReal.tsum_le_tsum fun rl ↦ mul_le_mul_right hinner _
    _ = (∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2))) *
          (ENNReal.ofReal dY + (ENNReal.ofReal dB + ENNReal.ofReal dB)) :=
        ENNReal.tsum_mul_right
    _ ≤ 1 * (ENNReal.ofReal dY + (ENNReal.ofReal dB + ENNReal.ofReal dB)) := by
        gcongr
        exact tsum_ofReal_firstPassageLaw_natCast_le_one g
    _ ≤ _ := by rw [one_mul]; exact hfinal

/-- The fresh law is summable on the common fresh deviation event. -/
theorem summable_trFreshLaw_c3FreshDev (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (g : ℕ) :
    Summable fun a : c3FreshDev ι n ↦ trFreshLaw n e g a :=
  summable_trFreshLaw_of_tsum_ofReal_ne_top
    ((tsum_trFreshLaw_c3FreshDev_le ι n e g).trans_lt ENNReal.ofReal_lt_top).ne

/-- **Mass of the common fresh deviation event**, as a real sum:
`μ_{e,g}(Dev^fr(ι)) ≤ U_v(ι) + U_d(ι)`. -/
@[collatz_pos_dens "lem_c3_fresh_dev_mass"]
theorem tsum_trFreshLaw_c3FreshDev_le_real (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (g : ℕ) :
    ∑' a : c3FreshDev ι n, trFreshLaw n e g a ≤ (Uv ι : ℝ) + Ud ι := by
  have h := tsum_trFreshLaw_c3FreshDev_le ι n e g
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _)
    (summable_trFreshLaw_c3FreshDev ι n e g)] at h
  have hU : (0 : ℝ) ≤ (Uv ι : ℝ) + Ud ι := by
    have h1 : (0 : ℝ) < Uv ι := by exact_mod_cast Uv_pos ι
    have h2 : (0 : ℝ) < Ud ι := by exact_mod_cast Ud_pos ι
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hU).1 h

end CollatzPosDens
