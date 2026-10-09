/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.StoppingTrace.TrBridgeGain
public import CollatzPosDens.StoppingTrace.TrBridgeLoss
public import CollatzPosDens.StoppingTrace.TrBridgeLossReal
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import CollatzPosDens.StoppingTrace.TrBridgeMassLe
public import CollatzPosDens.StoppingTrace.TrConcatShift
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrCountConcat
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaNonneg
public import CollatzPosDens.StoppingTrace.TrEntrySplit
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrGainLe
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrKernelOne
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrPassageBound
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# Two kernel steps, with the full surplus

Fix a level `n` and a unit `ξ ∈ G_n`; "black" and "white" refer to `(n, ξ, ε_*)`. For a black
point `v ∈ 𝒫` with `s = gap(v)`, write `y_π = x_{|π|}(v, π)` and
`a(π) = bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}` for `π ∈ Π_s`. The second power of the entry kernel
satisfies
```
m_2(v) ≤ (1 - d_*)² - (1 - d_*) δ_tr(s) - ∑_{π ∈ Π_s} a(π) Loss(y_π).
```
Every entry list from `v` splits uniquely as a passage `π ∈ Π_s` followed by a first-stop list
`b ∈ 𝒰(y_π)`, so `m_2(v) = ∑_π a(π) ∑_b a_{y_π}(b) m_1(x_{|b|}(y_π, b))`. Each endpoint
`x_{|b|}(y_π, b)` is black, so the one-step bound `m_1 ≤ 1 - d_* - δ_tr(gap)` applies, and the
inner sum is then at most `(1 - d_*) g_br(y_π) - H(y_π) = (1 - d_*) - Loss(y_π)`. Summing
against `a(π)` and using `∑_π a(π) ≤ 1 - d_* - δ_tr(s)` gives the bound.

## Main results

* `CollatzPosDens.trKernel_two_le`: the bound on `m_2(v)` for a black point `v`.
* `CollatzPosDens.trKernel_two_le_trBridgeLoss_eq`: at a point `y ∈ 𝒫` the bridge loss is
  a real number in `[0, 1 - d_*]`.
* `CollatzPosDens.trKernel_two_le_summable`: the series `∑_π a(π) Loss(y_π)` converges.

## Implementation notes

The value `m_2(v)` lies in `[0, ∞]` and the bridge loss in `[-∞, ∞]`. The bound is stated as an
inequality in `EReal` between `m_2(v)` and a real number, which loses nothing: it asserts that
`m_2(v)` is finite and at most the right-hand side (in particular that the right-hand side is
nonnegative). In the series, the bridge loss enters through `EReal.toReal`; this is the value of
the loss, since at the points `y_π ∈ 𝒫` the loss is a real number
(`trKernel_two_le_trBridgeLoss_eq`), and the real series converges
(`trKernel_two_le_summable`), so its `tsum` is the sum `∑_π a(π) Loss(y_π)`. The hypotheses
`n ≥ 1` and `J = ⌊n/2⌋` of the paper's statement are not needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.5.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n}

/-- Passage decomposition of every kernel step: for `s = gap(v)`,
`m_{k+1}(v) = ∑_{π ∈ Π_s} a(π) ∑_{b ∈ 𝒰(y_π)} a_{y_π}(b) m_k(x_{|b|}(y_π, b))`. -/
private theorem trKernel_succ_eq_tsum_trPassage (k : ℕ) (v : ℤ × ℤ) :
    trKernel n ξ (k + 1) v =
      ∑' π : trPassage (trGap n ξ (epsStar : ℝ) v),
        ENNReal.ofReal (trListWeight π.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length)) *
            ∑' b : trFirstStopSet n ξ (epsStar : ℝ) (trPath v π.1 π.1.length),
              ENNReal.ofReal (trListWeight b.1) *
                ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) *
                  trCount n ξ (trPath v π.1 π.1.length) b.1 b.1.length)) *
                trKernel n ξ k (trPath (trPath v π.1 π.1.length) b.1 b.1.length) := by
  classical
  set s := trGap n ξ (epsStar : ℝ) v
  set F : List (List ℤ × ℤ) → ℝ≥0∞ := fun u ↦
    ENNReal.ofReal (trListWeight u) *
      ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length)) *
        trKernel n ξ k (trPath v u u.length) with hF
  set A : List (List ℤ × ℤ) → ℝ≥0∞ := fun π ↦
    ENNReal.ofReal (trListWeight π) *
      ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length)) with hA
  set G : List (List ℤ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞ := fun π b ↦
    ENNReal.ofReal (trListWeight b) *
      ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) *
        trCount n ξ (trPath v π π.length) b b.length)) *
      trKernel n ξ k (trPath (trPath v π π.length) b b.length) with hG
  set S := {p : List (List ℤ × ℤ) × List (List ℤ × ℤ) | p.1 ∈ trPassage s ∧
        p.2 ∈ trFirstStopSet n ξ (epsStar : ℝ) (trPath v p.1 p.1.length)}
  have hbij := trEntryWords_bijOn_append n ξ (epsStar : ℝ) v
  have h1 : trKernel n ξ (k + 1) v = ∑' u : trEntryWords n ξ (epsStar : ℝ) v, F u.1 := by
    rw [trKernel_succ]
  have h2 : ∑' u : trEntryWords n ξ (epsStar : ℝ) v, F u.1 = ∑' p : S, F (p.1.1 ++ p.1.2) :=
    ((hbij.equiv _).tsum_eq (fun u : trEntryWords n ξ (epsStar : ℝ) v ↦ F u.1)).symm
  have hfac : ∀ π b : List (List ℤ × ℤ), F (π ++ b) = A π * G π b := by
    intro π b
    simp only [hF, hA, hG, trListWeight_append, List.length_append]
    rw [trCount_concat ξ v π b rfl, trPath_append_add v π b rfl, mul_add, Real.exp_add,
      ENNReal.ofReal_mul (trListWeight_nonneg _), ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  rw [h1, h2, tsum_subtype S (fun p ↦ F (p.1 ++ p.2)),
    tsum_subtype (trPassage s) (fun π ↦ A π *
      ∑' b : trFirstStopSet n ξ (epsStar : ℝ) (trPath v π π.length), G π b.1)]
  refine (ENNReal.tsum_prod (f := fun a b ↦ S.indicator (fun p ↦ F (p.1 ++ p.2)) (a, b))).trans ?_
  refine tsum_congr fun π ↦ ?_
  by_cases hπ : π ∈ trPassage s
  · rw [Set.indicator_of_mem hπ, ← ENNReal.tsum_mul_left,
      tsum_subtype (trFirstStopSet n ξ (epsStar : ℝ) (trPath v π π.length))
        (fun b ↦ A π * G π b)]
    refine tsum_congr fun b ↦ ?_
    by_cases hb : b ∈ trFirstStopSet n ξ (epsStar : ℝ) (trPath v π π.length)
    · rw [Set.indicator_of_mem (show (π, b) ∈ S from ⟨hπ, hb⟩), Set.indicator_of_mem hb, hfac]
    · rw [Set.indicator_of_notMem (show (π, b) ∉ S from fun h ↦ hb h.2),
        Set.indicator_of_notMem hb]
  · rw [Set.indicator_of_notMem hπ]
    refine ENNReal.tsum_eq_zero.2 fun b ↦ ?_
    exact Set.indicator_of_notMem (show (π, b) ∉ S from fun h ↦ hπ h.1) _

/-- At a point `y ∈ 𝒫` the bridge loss is a real number in `[0, 1 - d_*]`. -/
theorem trKernel_two_le_trBridgeLoss_eq (hξ : IsResidueUnit ξ) {y : ℤ × ℤ} (hy : y ∈ bkPoints) :
    trBridgeLoss n ξ y = ((trBridgeLoss n ξ y).toReal : EReal) ∧
      0 ≤ (trBridgeLoss n ξ y).toReal ∧ (trBridgeLoss n ξ y).toReal ≤ 1 - (dStar : ℝ) := by
  rw [trBridgeLoss_eq_coe_trBridgeLossReal hξ hy, EReal.toReal_coe]
  exact ⟨rfl, trBridgeLossReal_nonneg n ξ y, trBridgeLossReal_le hξ hy⟩

/-- The tilted passage weight `a(π) = bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}` is nonnegative. -/
private lemma passageWeight_nonneg (v : ℤ × ℤ) (π : List (List ℤ × ℤ)) :
    0 ≤ trListWeight π * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length) :=
  mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le

/-- Summability of `∑_π a(π) f(π)` for `0 ≤ f ≤ 1 - d_*`. -/
private lemma summable_mul_of_le (v : ℤ × ℤ) (s : ℕ) (f : trPassage s → ℝ)
    (h0 : ∀ π, 0 ≤ f π) (h1 : ∀ π, f π ≤ 1 - (dStar : ℝ)) :
    Summable fun π : trPassage s ↦
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) * f π :=
  ((summable_trPassage_mul_exp_neg_trCount ξ v s).mul_right (1 - (dStar : ℝ))).of_nonneg_of_le
    (fun π ↦ mul_nonneg (passageWeight_nonneg v π.1) (h0 π))
    (fun π ↦ mul_le_mul_of_nonneg_left (h1 π) (passageWeight_nonneg v π.1))

/-- At a point `v ∈ 𝒫`, the series `∑_{π ∈ Π_s} a(π) Loss(y_π)` converges. -/
theorem trKernel_two_le_summable (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (s : ℕ) :
    Summable fun π : trPassage s ↦
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) *
        (trBridgeLoss n ξ (trPath v π.1 π.1.length)).toReal :=
  summable_mul_of_le v s _
    (fun π ↦ (trKernel_two_le_trBridgeLoss_eq hξ (trPath_mem_bkPoints hv π.1 _)).2.1)
    (fun π ↦ (trKernel_two_le_trBridgeLoss_eq hξ (trPath_mem_bkPoints hv π.1 _)).2.2)

/-- The inner sum of the second kernel step: for `y ∈ 𝒫`,
`∑_{b ∈ 𝒰(y)} a_y(b) m_1(x_{|b|}(y, b)) ≤ (1 - d_*) - Loss(y)`. -/
private lemma inner_le (hξ : IsResidueUnit ξ) {y : ℤ × ℤ} (hy : y ∈ bkPoints) :
    ∑' b : trFirstStopSet n ξ (epsStar : ℝ) y,
        ENNReal.ofReal (trListWeight b.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b.1 b.1.length)) *
          trKernel n ξ 1 (trPath y b.1 b.1.length) ≤
      ENNReal.ofReal (1 - (dStar : ℝ) - trBridgeLossReal n ξ y) := by
  set c : ℝ := 1 - (dStar : ℝ)
  set B : trFirstStopSet n ξ (epsStar : ℝ) y → ℝ≥0∞ := fun b ↦
    ENNReal.ofReal (trListWeight b.1) *
      ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b.1 b.1.length))
  set δb : trFirstStopSet n ξ (epsStar : ℝ) y → ℝ := fun b ↦
    trDelta (trGap n ξ (epsStar : ℝ) (trPath y b.1 b.1.length))
  have hδc : ∀ b, δb b ≤ c := fun b ↦
    trDelta_trGap_le_one_sub_dStar hξ (trPath_mem_bkPoints hy b.1 _)
      (trFirstStopSet_bkBlack b.2)
  calc _ ≤ ∑' b, B b * ENNReal.ofReal (c - δb b) := by
        refine ENNReal.tsum_le_tsum fun b ↦ ?_
        gcongr
        exact trKernel_one_le hξ (trPath_mem_bkPoints hy b.1 _) (trFirstStopSet_bkBlack b.2)
    _ = ENNReal.ofReal (c - trBridgeLossReal n ξ y) := by
        have hH := trBridgeGain_ne_top hξ hy
        refine (ENNReal.add_left_inj hH).1 ?_
        have e1 : ∑' b, B b * ENNReal.ofReal (c - δb b) + trBridgeGain n ξ y =
            ENNReal.ofReal c * trBridgeMass n ξ y := by
          rw [trBridgeGain_def, trBridgeMass_def, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun b ↦ ?_
          rw [max_eq_left (trDelta_nonneg _), ← mul_add,
            ← ENNReal.ofReal_add (sub_nonneg.2 (hδc b)) (trDelta_nonneg _), sub_add_cancel,
            mul_comm]
        have e2 : ENNReal.ofReal (c - trBridgeLossReal n ξ y) + trBridgeGain n ξ y =
            ENNReal.ofReal c * trBridgeMass n ξ y := by
          have hle := toReal_trBridgeGain_le hξ hy
          have hcl : c - trBridgeLossReal n ξ y =
              c * (trBridgeMass n ξ y).toReal - (trBridgeGain n ξ y).toReal := by
            simp only [trBridgeLossReal, c]
            ring
          rw [hcl]
          conv_lhs => arg 2; rw [← ENNReal.ofReal_toReal hH]
          rw [← ENNReal.ofReal_add (sub_nonneg.2 hle) ENNReal.toReal_nonneg, sub_add_cancel,
            ENNReal.ofReal_mul one_sub_dStar_pos.le,
            ENNReal.ofReal_toReal (trBridgeMass_ne_top n ξ y)]
        rw [e1, e2]

/-- **Two kernel steps, with the full surplus.** Let `ξ ∈ G_n` be a unit and `v ∈ 𝒫` a black
point, `s = gap(v)`. Then
`m_2(v) ≤ (1 - d_*)² - (1 - d_*) δ_tr(s) - ∑_{π ∈ Π_s} a(π) Loss(x_{|π|}(v, π))`, where
`a(π) = bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}`, the inequality being in `EReal` (so `m_2(v)` is
finite). -/
@[collatz_pos_dens "lem_tr_kernel_two_bound"]
theorem trKernel_two_le (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) :
    (trKernel n ξ 2 v : EReal) ≤
      (((1 - (dStar : ℝ)) ^ 2 - (1 - (dStar : ℝ)) * trDelta (trGap n ξ (epsStar : ℝ) v) -
        ∑' π : trPassage (trGap n ξ (epsStar : ℝ) v),
          trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) *
            (trBridgeLoss n ξ (trPath v π.1 π.1.length)).toReal : ℝ) : EReal) := by
  set s := trGap n ξ (epsStar : ℝ) v
  set c : ℝ := 1 - (dStar : ℝ)
  have hc := one_sub_dStar_pos
  set a : trPassage s → ℝ := fun π ↦
    trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) with ha
  set L : trPassage s → ℝ := fun π ↦ trBridgeLossReal n ξ (trPath v π.1 π.1.length)
  have hy : ∀ π : trPassage s, trPath v π.1 π.1.length ∈ bkPoints :=
    fun π ↦ trPath_mem_bkPoints hv π.1 _
  have hL0 : ∀ π, 0 ≤ L π := fun π ↦ trBridgeLossReal_nonneg n ξ _
  have hLc : ∀ π, L π ≤ c := fun π ↦ trBridgeLossReal_le hξ (hy π)
  have ha0 : ∀ π, 0 ≤ a π := fun π ↦ passageWeight_nonneg v π.1
  have hsaL : Summable fun π ↦ a π * L π := summable_mul_of_le v s L hL0 hLc
  have hsacL : Summable fun π ↦ a π * (c - L π) :=
    summable_mul_of_le v s (fun π ↦ c - L π) (fun π ↦ sub_nonneg.2 (hLc π))
      (fun π ↦ by linarith [hL0 π])
  have hpass : ∑' π, a π ≤ c - trDelta s := tsum_trPassage_mul_exp_neg_trCount_le hξ hv hb
  set X : ℝ := ∑' π, a π * (c - L π) with hX
  have hX0 : 0 ≤ X := tsum_nonneg fun π ↦ mul_nonneg (ha0 π) (sub_nonneg.2 (hLc π))
  have hm : trKernel n ξ 2 v ≤ ENNReal.ofReal X := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, trKernel_succ_eq_tsum_trPassage]
    calc _ ≤ ∑' π : trPassage s, ENNReal.ofReal (a π * (c - L π)) := by
          refine ENNReal.tsum_le_tsum fun π ↦ ?_
          rw [ENNReal.ofReal_mul (ha0 π), ENNReal.ofReal_mul (trListWeight_nonneg _)]
          gcongr
          exact inner_le hξ (hy π)
      _ = ENNReal.ofReal X :=
          (ENNReal.ofReal_tsum_of_nonneg
            (fun π ↦ mul_nonneg (ha0 π) (sub_nonneg.2 (hLc π))) hsacL).symm
  have hXle : X ≤ c ^ 2 - c * trDelta s - ∑' π, a π * L π := by
    have : X = c * ∑' π, a π - ∑' π, a π * L π := by
      rw [hX, ← tsum_mul_left,
        ← ((summable_trPassage_mul_exp_neg_trCount ξ v s).mul_left c).tsum_sub hsaL]
      exact tsum_congr fun π ↦ by ring
    rw [this]
    nlinarith
  have hsum : ∑' π : trPassage s, a π * (trBridgeLoss n ξ (trPath v π.1 π.1.length)).toReal =
      ∑' π, a π * L π := tsum_congr fun π ↦ by
    rw [trBridgeLoss_eq_coe_trBridgeLossReal hξ (hy π), EReal.toReal_coe]
  calc (trKernel n ξ 2 v : EReal) ≤ ((ENNReal.ofReal X : ℝ≥0∞) : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.2 hm
    _ = (X : EReal) := by rw [EReal.coe_ennreal_ofReal, max_eq_left hX0]
    _ ≤ _ := by
        refine EReal.coe_le_coe_iff.2 ?_
        simp only [ha] at hsum
        rw [hsum]
        exact hXle

end CollatzPosDens
