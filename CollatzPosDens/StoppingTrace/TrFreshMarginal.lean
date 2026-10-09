/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockHold
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnListMarginal
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrListSplit
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass

/-!
# The displacement marginal of the fresh law

Let `J = ⌊n/2⌋`, `v ≤ J`, and let `G : (ℕ × ℤ) × 𝒫^v → [0, ∞]`. Summing the fresh law
`μ_{e,g}((r, ℓ), β) = F_g(r, ℓ) bw^⊗(β)` against `G` evaluated at the displacement `(r, ℓ)` and the
block points of the first `v` blocks of `β` gives
`∑_{((r, ℓ), β) ∈ 𝒜_n} μ_{e,g}((r, ℓ), β) G((r, ℓ), (bpt(β¹), …, bpt(βᵛ)))
  = ∑_{(r, ℓ)} F_g(r, ℓ) ∑_{h ∈ 𝒫^v} η^{⊗v}(h) G((r, ℓ), h)`.

Writing `β = β_{[1,v]} β_{[v+1,J]}`, the list weight splits as a product, the last `J - v`
blocks enter only through their weight, of total mass `1`, and grouping the first `v` blocks by
their block points turns the weight `bw^⊗` into the hold-list weight `η^{⊗v}`, since
`η(h) = ∑_{bpt(β) = h} bw(β)` for each `h ∈ 𝒫`.

## Main results

* `CollatzPosDens.tsum_trFreshLaw_mul_chBlockPoint`: the marginal identity.
* `CollatzPosDens.tsum_holdListLaw_bkPoints_mul_indicator_le`: an event on `𝒫^v` has
  `η^{⊗v}`-mass at most that of any event on `(ℕ × ℤ)^v` containing its image.
* `CollatzPosDens.tsum_ofReal_holdListLaw_bkPoints_le_one`: `η^{⊗v}` has mass at most `1` on
  `𝒫^v`.

## Implementation notes

All sums are unconditional sums in `[0, ∞]`; the real weights `F_g`, `bw^⊗`, `η^{⊗v}` enter
through `ENNReal.ofReal`. The test function `G` is curried and defined on all of
`(ℕ × ℤ) × (ℤ × ℤ)^v`; only its values on `(ℕ × ℤ) × 𝒫^v` enter. The sum over `𝒫^v` runs over
the tuples `h : Fin v → ℤ × ℤ` with every entry in `𝒫`, and `η^{⊗v}(h)` is `holdListLaw` of the
tuple `i ↦ (j(h_i), l(h_i))`, the first coordinate read in `ℕ`. The identity holds without the
hypotheses `n ≥ 1` and `e ∈ 𝒫`, and without a unit `ξ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The blocks with block point `h ∈ 𝒫` have total weight `η(h)`, as a sum in `[0, ∞]`. -/
private lemma trFreshMarginal_fiber {h : ℤ × ℤ} (hh : h ∈ bkPoints) :
    ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint β = h},
      ENNReal.ofReal (chBlockWeight β.1) = ENNReal.ofReal (holdLaw h.1.toNat h.2) := by
  rw [holdLaw_eq_tsum_chBlockWeight hh]
  refine (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ chBlockWeight_nonneg _) ?_).symm
  have hs := (hasSum_prod_chBlockWeight_single).summable
  refine hs.comp_injective (i := fun β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧
    chBlockPoint β = h} ↦ (⟨β.1, β.2.1⟩ : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)})) ?_
  intro x y hxy
  exact Subtype.ext (congrArg Subtype.val hxy :)

/-- The tuples of blocks with prescribed block points `h`. -/
private def trFreshMarginalFiberEquiv {v : ℕ}
    (gmap : (Fin v → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}) →
      {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints})
    (hg : ∀ x i, (gmap x).1 i = chBlockPoint (x i).1)
    (h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints}) :
    {x // gmap x = h} ≃
      ∀ i, {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint β = h.1 i} where
  toFun x i := ⟨(x.1 i).1, (x.1 i).2, by rw [← hg, x.2]⟩
  invFun y := ⟨fun i ↦ ⟨(y i).1, (y i).2.1⟩,
    Subtype.ext (funext fun i ↦ by rw [hg]; exact (y i).2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Grouping tuples of blocks by their block points:
`∑_{x ∈ 𝔅^v} ∏_i bw(xᵢ) Φ(bpt(x₁), …, bpt(x_v)) = ∑_{h ∈ 𝒫^v} η^{⊗v}(h) Φ(h)`. -/
private lemma trFreshMarginal_group (v : ℕ) (Φ : (Fin v → ℤ × ℤ) → ℝ≥0∞) :
    ∑' x : Fin v → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (∏ i, chBlockWeight (x i).1) * Φ (fun i ↦ chBlockPoint (x i).1) =
      ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) * Φ h.1 := by
  let gmap : (Fin v → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}) →
      {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints} :=
    fun x ↦ ⟨fun i ↦ chBlockPoint (x i).1, fun i ↦ chBlockPoint_mem_bkPoints _⟩
  rw [← (Equiv.sigmaFiberEquiv gmap).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun h ↦ ?_
  have hΦ : ∀ x : {x // gmap x = h}, Φ (fun i ↦ chBlockPoint (x.1 i).1) = Φ h.1 :=
    fun x ↦ congrArg Φ (congrArg Subtype.val x.2)
  simp only [Equiv.sigmaFiberEquiv_apply, hΦ]
  rw [ENNReal.tsum_mul_right]
  congr 1
  rw [← (trFreshMarginalFiberEquiv gmap (fun _ _ ↦ rfl) h).symm.tsum_eq]
  simp only [trFreshMarginalFiberEquiv, Equiv.coe_fn_symm_mk]
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ chBlockWeight_nonneg _)]
  rw [tsum_pi_fin_prod_ennreal (fun i (β : {β : List ℤ × ℤ //
    β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint β = h.1 i}) ↦ ENNReal.ofReal (chBlockWeight β.1)),
    holdListLaw_def, ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ holdLaw_nonneg _ _)]
  exact Finset.prod_congr rfl fun i _ ↦ trFreshMarginal_fiber (h.2 i)

/-- The block-list marginal: for `v ≤ J`,
`∑_{β ∈ 𝔅^J} bw^⊗(β) Φ(bpt(β¹), …, bpt(βᵛ)) = ∑_{h ∈ 𝒫^v} η^{⊗v}(h) Φ(h)`. -/
private lemma trFreshMarginal_blocks {J v : ℕ} (hv : v ≤ J) (Φ : (Fin v → ℤ × ℤ) → ℝ≥0∞) :
    ∑' β : {β : List (List ℤ × ℤ) //
        β.length = J ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
        ENNReal.ofReal (trListWeight β.1) *
          Φ (fun i ↦ chBlockPoint (β.1[(i : ℕ)]'(by have := β.2.1; omega))) =
      ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) * Φ h.1 := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hv
  set Ψ : List (List ℤ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞ :=
    fun u _ ↦ Φ (fun i ↦ chBlockPoint (u.getD i ([], 0))) with hΨ
  have step : ∀ β : {β : List (List ℤ × ℤ) //
      β.length = v + w ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
      Φ (fun i ↦ chBlockPoint (β.1[(i : ℕ)]'(by have := β.2.1; omega))) =
        Ψ (trSublist β.1 1 v) (trSublist β.1 (v + 1) (v + w)) := by
    intro β
    simp only [hΨ, trSublist_one]
    congr 1
    funext i
    have : (i : ℕ) < β.1.length := by have := β.2.1; omega
    simp [this]
  simp_rw [step]
  rw [tsum_trListWeight_trSublist]
  have hmass : ∀ u : {u : List (List ℤ × ℤ) //
      u.length = v ∧ ∀ x ∈ u, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
      ∑' f : {f : List (List ℤ × ℤ) //
          f.length = w ∧ ∀ x ∈ f, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
        ENNReal.ofReal (trListWeight u.1) * ENNReal.ofReal (trListWeight f.1) * Ψ u.1 f.1 =
        ENNReal.ofReal (trListWeight u.1) * Ψ u.1 [] := fun u ↦ by
    simp_rw [mul_right_comm _ _ (Ψ _ _), hΨ]
    rw [ENNReal.tsum_mul_left, tsum_ofReal_trListWeight_length_eq, mul_one]
  simp_rw [hmass]
  rw [← (blockListEquivFin v).symm.tsum_eq, ← trFreshMarginal_group]
  refine tsum_congr fun x ↦ ?_
  simp only [blockListEquivFin, Equiv.coe_fn_symm_mk, trListWeight_ofFn, hΨ]
  congr 2
  funext i
  simp

/-- **Displacement marginal of the fresh law.** For `v ≤ ⌊n/2⌋` and `G` with values in `[0, ∞]`,
`∑_{((r, ℓ), β) ∈ 𝒜_n} μ_{e,g}((r, ℓ), β) G((r, ℓ), (bpt(β¹), …, bpt(βᵛ)))
  = ∑_{(r, ℓ) ∈ ℕ × ℤ} F_g(r, ℓ) ∑_{h ∈ 𝒫^v} η^{⊗v}(h) G((r, ℓ), h)`. -/
@[collatz_pos_dens "lem_tr_fresh_marginal"]
theorem tsum_trFreshLaw_mul_chBlockPoint (n : ℕ) (e : ℤ × ℤ) (g v : ℕ) (hv : v ≤ n / 2)
    (G : ℕ × ℤ → (Fin v → ℤ × ℤ) → ℝ≥0∞) :
    ∑' a : trAtoms n, ENNReal.ofReal (trFreshLaw n e g a) *
        G a.1.1 (fun i ↦ chBlockPoint (a.1.2[(i : ℕ)]'(by
          have := (mem_trAtoms.1 a.2).1; omega))) =
      ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) *
        ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
          ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) * G rl h.1 := by
  rw [← (trAtomsEquiv n).symm.tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun rl ↦ ?_
  rw [← trFreshMarginal_blocks hv (G rl), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun β ↦ ?_
  simp only [trAtomsEquiv, Equiv.coe_fn_symm_mk, trFreshLaw_def]
  rw [ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _), mul_assoc]

/-- Reindexing a hold-list event from tuples of points of `𝒫` to tuples in `ℕ × ℤ`: if every
`h ∈ 𝒫^v` with `ψ h` reads as a tuple `i ↦ (j(hᵢ), l(hᵢ))` satisfying `Φ`, then the
`η^{⊗v}`-mass of `ψ` is at most that of `Φ`. -/
theorem tsum_holdListLaw_bkPoints_mul_indicator_le {v : ℕ} (ψ : (Fin v → ℤ × ℤ) → Prop)
    (Φ : (Fin v → ℕ × ℤ) → Prop)
    (hψ : ∀ h : Fin v → ℤ × ℤ, (∀ i, h i ∈ bkPoints) → ψ h →
      Φ (fun i ↦ ((h i).1.toNat, (h i).2))) :
    ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
          {h | ψ h}.indicator 1 h.1 ≤
      ∑' u : {u : Fin v → ℕ × ℤ // (∀ i, 1 ≤ (u i).1) ∧ Φ u},
        ENNReal.ofReal (holdListLaw u.1) := by
  set F := {u : Fin v → ℕ × ℤ | (∀ i, 1 ≤ (u i).1) ∧ Φ u}.indicator
    (fun u ↦ ENNReal.ofReal (holdListLaw u)) with hF
  set g : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints} → (Fin v → ℕ × ℤ) :=
    fun h i ↦ ((h.1 i).1.toNat, (h.1 i).2) with hg
  have hinj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    funext i
    have h1 := congrFun hab i
    simp only [g, Prod.mk.injEq] at h1
    have ha := a.2 i
    have hb := b.2 i
    simp only [mem_bkPoints, bkJ] at ha hb
    ext
    · omega
    · exact h1.2
  calc _ ≤ ∑' h, F (g h) := by
        refine ENNReal.tsum_le_tsum fun h ↦ ?_
        by_cases hh : ψ h.1
        · have hmem : g h ∈ {u : Fin v → ℕ × ℤ | (∀ i, 1 ≤ (u i).1) ∧ Φ u} := by
            refine ⟨fun i ↦ ?_, hψ h.1 h.2 hh⟩
            have := h.2 i
            simp only [mem_bkPoints, bkJ] at this
            simp only [g]
            omega
          rw [Set.indicator_of_mem (show h.1 ∈ {h | ψ h} from hh), Pi.one_apply, mul_one, hF,
            Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem (show h.1 ∉ {h | ψ h} from hh), mul_zero]
          exact zero_le
    _ ≤ ∑' u, F u := ENNReal.tsum_comp_le_tsum_of_injective hinj F
    _ = _ := (tsum_subtype {u : Fin v → ℕ × ℤ | (∀ i, 1 ≤ (u i).1) ∧ Φ u}
        (fun u ↦ ENNReal.ofReal (holdListLaw u))).symm

/-- The hold-list law `η^{⊗v}` has total mass at most `1` on `𝒫^v`, as a sum in `[0, ∞]`. -/
theorem tsum_ofReal_holdListLaw_bkPoints_le_one (v : ℕ) :
    ∑' h : {h : Fin v → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) ≤ 1 := by
  have h := tsum_holdListLaw_bkPoints_mul_indicator_le (v := v) (fun _ ↦ True) (fun _ ↦ True)
    (fun _ _ _ ↦ trivial)
  simp only [Set.ofPred_true, Set.indicator_univ, Pi.one_apply, mul_one] at h
  refine h.trans (le_of_eq ?_)
  rw [← (Equiv.subtypeEquivRight (fun u : Fin v → ℕ × ℤ ↦
    (⟨fun h ↦ ⟨h, trivial⟩, fun h ↦ h.1⟩ :
      (∀ i, 1 ≤ (u i).1) ↔ (∀ i, 1 ≤ (u i).1) ∧ True))).tsum_eq]
  simp only [Equiv.subtypeEquivRight_apply_coe]
  exact tsum_ofReal_holdListLaw v

end CollatzPosDens
