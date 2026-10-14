/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Group.Indicator
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.Dbad
public import CollatzPosDens.Transfer.Dsc
public import CollatzPosDens.Transfer.H
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.PT
public import CollatzPosDens.Transfer.PW
public import CollatzPosDens.Transfer.Qpack
public import CollatzPosDens.Transfer.Budget
public import CollatzPosDens.Transfer.Cont
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrEstar
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrWhiteCount
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkRightEdge
public import CollatzPosDens.Case3.C3BadMass
public import CollatzPosDens.Case3.C3Continuation
public import CollatzPosDens.Case3.C3EstarMass
public import CollatzPosDens.Case3.C3ScaleRoom
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.CharSum.ChBoundaryStep
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.Renewal.RnListMarginal
public import CollatzPosDens.Transfer.PBits
public import CollatzPosDens.Transfer.BudgetLem
public import CollatzPosDens.Transfer.ContLem
public import CollatzPosDens.Transfer.WhiteTerm
public import CollatzPosDens.StoppingTrace.TrFreshMarginal
public import CollatzPosDens.StoppingTrace.TrSurvivalExport

/-!
# Case 3 of the monotonicity step

Let `ξ` be a unit, `m` an integer with `m ≥ D_sc`, `m ≥ D_bad` and `m ≤ J = ⌊n/2⌋`, and
`e ∈ 𝒫` with `j(e) + m = J`. Suppose `e ∈ Δ` for a triangle `Δ ∈ 𝔗_{n,ξ,ε_*}` whose corner lies
far above `e`: `l_Δ - l(e) > m / (log m)^2`. Then
$$\mathsf Q(e) \le m^{-A_*}\,\mathsf Q_{m-1},$$
both sides formed with `ε = ε_*` and `A = A_*`.

Write `g = l_Δ - l(e)`. The continuation lemma (at `P = P_*`) bounds `Q(e)` by the average,
over the fresh law `μ_{e,g}`, of `e^{-z_* N(a)} Q(y^e_{P_*}(a))`, `N(a)` the weighted white count
up to time `P_* - 1`. On an atom of positive mass the advance `Adv(a) = j(y^e_{P_*}(a)) - j(e)` is
at least `1`, so the boundary step bounds `Q(y^e_{P_*}(a))` by
`max(m - Adv(a), 1)^{-A_*} Q_{m-1}`. Off `Bad^e_m` this is at most
`(400/83)^{A_*} m^{-A_*} Q_{m-1} ≤ c_cont m^{-A_*} Q_{m-1}`, and off `Low^e` moreover
`e^{-z_* N(a)} (400/83)^{A_*} ≤ e^{-101 z_*} (400/83)^{A_*} < 1/P_W`. Summing against `μ_{e,g}`,
the masses of `Bad^e_m`, of `Low^e \ Bad^e_m` and of the whole law are controlled by the outer
horizontal tail, by the survival export together with the large-triangle mass, and by the total
mass `≤ 1`; the bracket is then below the six-term budget `Bud < 1`.

## Main results

* `CollatzPosDens.chQ_le_rpow_mul_chQm_of_gap_gt`: the statement.
* `CollatzPosDens.chQ_le_rpow_mul_chQm_of_gap_gt_natCast_mul_log_two_le`: the
  vertical gap `g = l_Δ - l(e)` satisfies `g log 2 ≤ m log 9`.
* `CollatzPosDens.chQ_le_rpow_mul_chQm_of_gap_gt_tsum_le_one`: the fresh law has total
  mass at most `1` on the atoms.

## Implementation notes

The hypotheses `n ≥ 1`, `e ∈ 𝒫` and `m ≤ ⌊n/2⌋` of the source are omitted: `e ∈ 𝒫` follows from
`e ∈ Δ`, and then `m ≤ ⌊n/2⌋` (hence `n ≥ 1`) follows from `j(e) + m = ⌊n/2⌋`. The integer
`m ≥ D_sc ≥ 2` is taken in `ℕ`, and `m^{-A_*}` is the real power `(m : ℝ) ^ (-A_*)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- If `e ∈ Δ ∈ 𝔗_{n,ξ,ε_*}` with `j(e) + m = ⌊n/2⌋` and `l(e) + g = l_Δ`, then
`g log 2 ≤ m log 9`. -/
theorem chQ_le_rpow_mul_chQm_of_gap_gt_natCast_mul_log_two_le {n : ℕ}
    {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {m : ℕ} {e : ℤ × ℤ}
    (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {Δ : BkTriangle}
    (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ)) (heΔ : e ∈ Δ) {g : ℕ} (hg : bkL e + g = Δ.l) :
    (g : ℝ) * log 2 ≤ m * log 9 := by
  obtain ⟨hε₀, hε⟩ := epsStar_mem_bkRange (K := ℝ)
  have hedge := j_add_s_div_log_nine_lt_of_mem_bkFamily hξ hε₀ hε hΔ
  have hn : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : n ≤ 2 * (n / 2) + 1)
    linarith
  have hs : Δ.s ≤ (((n / 2 : ℕ) : ℝ) - Δ.j) * log 9 := by
    rw [← div_le_iff₀ (log_pos (by norm_num))]
    linarith
  have hw := heΔ.2.2
  rw [← hg, add_sub_cancel_left, Int.cast_natCast] at hw
  have hjR : ((bkJ e + m : ℤ) : ℝ) = (((n / 2 : ℕ) : ℤ) : ℝ) := by rw [hje]
  rw [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at hjR
  push_cast at hw
  linear_combination hw + hs - log 9 * hjR

/-- The fresh law `μ_{e,g}` has total mass at most `1` on the atoms `𝒜_n`. -/
theorem chQ_le_rpow_mul_chQm_of_gap_gt_tsum_le_one (n : ℕ) (e : ℤ × ℤ) (g : ℕ) :
    ∑' a : trAtoms n, ENNReal.ofReal (trFreshLaw n e g a) ≤ 1 := by
  have h := tsum_trFreshLaw_mul_chBlockPoint n e g 0 (Nat.zero_le _) (fun _ _ ↦ 1)
  simp only [mul_one] at h
  rw [h]
  have hin : ∑' h : {h : Fin 0 → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
      ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) = 1 := by
    have : Unique {h : Fin 0 → ℤ × ℤ // ∀ i, h i ∈ bkPoints} :=
      ⟨⟨⟨Fin.elim0, fun i ↦ i.elim0⟩⟩, fun h ↦ Subtype.ext (funext fun i ↦ i.elim0)⟩
    rw [tsum_fintype, Fintype.sum_unique, holdListLaw_zero, ENNReal.ofReal_one]
  rw [tsum_congr fun _ ↦ by rw [hin, mul_one]]
  exact tsum_ofReal_firstPassageLaw_natCast_le_one g

/-- The pointwise weight bound behind Case 3: with `X ≤ ρ m^{-A}` off `B`, `ρ ≤ c`, `E ≤ η` off
`L` and `η ρ ≤ w`, the product `μ E X` is at most
`m^{-A} (m^A μ 1_B + c μ 1_{L \ B} + w μ)`. -/
private lemma c3Case3_atom_le {α : Type*} (B L : Set α) (a : α) {μa E X Mi Mp η ρ c w : ℝ}
    (hμ : 0 ≤ μa) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hMi : 0 ≤ Mi)
    (hMM : Mi * Mp = 1) (hρ : a ∉ B → X ≤ ρ * Mi) (hρc : ρ ≤ c) (hη : a ∉ L → E ≤ η)
    (hηρ : η * ρ ≤ w) (hw : 0 ≤ w) :
    μa * E * X ≤ Mi * (Mp * B.indicator (fun _ ↦ μa) a + c * (L \ B).indicator (fun _ ↦ μa) a +
      w * μa) := by
  have hEX1 : E * X ≤ 1 := (mul_le_of_le_one_left hX0 hE1).trans hX1
  have hwμ : 0 ≤ Mi * (w * μa) := mul_nonneg hMi (mul_nonneg hw hμ)
  by_cases haB : a ∈ B
  · rw [Set.indicator_of_mem haB, Set.indicator_of_notMem (fun h ↦ h.2 haB), mul_zero,
      add_zero]
    have h1 : μa * (E * X) ≤ μa * 1 := mul_le_mul_of_nonneg_left hEX1 hμ
    have h2 : Mi * (Mp * μa) = μa := by rw [← mul_assoc, hMM, one_mul]
    nlinarith
  rw [Set.indicator_of_notMem haB, mul_zero, zero_add]
  have hX := hρ haB
  by_cases haL : a ∈ L
  · rw [Set.indicator_of_mem (show a ∈ L \ B from ⟨haL, haB⟩)]
    have h : E * X ≤ c * Mi := (mul_le_of_le_one_left hX0 hE1).trans
      (hX.trans (mul_le_mul_of_nonneg_right hρc hMi))
    nlinarith [mul_le_mul_of_nonneg_left h hμ]
  · rw [Set.indicator_of_notMem (fun h ↦ haL h.1), mul_zero, zero_add]
    have hE := hη haL
    have h : E * X ≤ w * Mi := calc
      E * X ≤ η * (ρ * Mi) := mul_le_mul hE hX hX0 (hE0.trans hE)
      _ = (η * ρ) * Mi := by ring
      _ ≤ w * Mi := mul_le_mul_of_nonneg_right hηρ hMi
    nlinarith [mul_le_mul_of_nonneg_left h hμ]

/-- If `κ m ≤ D` with `κ, m > 0` and `A ≥ 0`, then `D ^ (-A) ≤ κ⁻¹ ^ A * m ^ (-A)`. -/
theorem rpow_neg_le_inv_rpow_mul_rpow_neg {m D A κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hA : 0 ≤ A)
    (h : κ * m ≤ D) : D ^ (-A) ≤ κ⁻¹ ^ A * m ^ (-A) := by
  calc D ^ (-A) ≤ (κ * m) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hκ hm) h (neg_nonpos.2 hA)
    _ = κ⁻¹ ^ A * m ^ (-A) := by
        rw [Real.mul_rpow hκ.le hm.le, Real.rpow_neg hκ.le, ← Real.inv_rpow hκ.le]

/-- Off the bad atoms, the boundary weight `max(m - r, 1)^{-A}` is at most `(400/83)^A m^{-A}`,
where `r` is the advance of the fresh path. -/
theorem rpow_neg_max_sub_le_of_notMem_trBad {n : ℕ} {e : ℤ × ℤ} {m : ℕ} (hm : 0 < m) {A : ℝ}
    (hA : 0 ≤ A) {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n) (hb : a ∉ trBad n e m)
    {r : ℕ} (hr : (r : ℤ) = bkJ (trFreshPath e a pStar) - bkJ e) :
    ((max ((m : ℤ) - r) 1 : ℤ) : ℝ) ^ (-A) ≤ (400 / 83 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
  have h := lt_of_notMem_trBad ha hb
  rw [← hr] at h
  have hZ : 83 * (m : ℤ) < 400 * max ((m : ℤ) - r) 1 :=
    (show 83 * (m : ℤ) < 400 * ((m : ℤ) - r) by omega).trans_le
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  have hR : (83 / 400 : ℝ) * m ≤ ((max ((m : ℤ) - r) 1 : ℤ) : ℝ) := by
    have : ((83 * (m : ℤ) : ℤ) : ℝ) ≤ ((400 * max ((m : ℤ) - r) 1 : ℤ) : ℝ) := by
      exact_mod_cast hZ.le
    push_cast at this ⊢
    linarith
  have := rpow_neg_le_inv_rpow_mul_rpow_neg (by exact_mod_cast hm) (by norm_num) hA hR
  rwa [inv_div] at this

/-- The Case 3 bound on a charged atom `a ∈ 𝒜_n`: its contribution to the continuation sum for
`Q(e)` is at most `m^{-A} (m^A μ 1_B + c μ 1_{L \ B} + μ / P_W) Q_{m-1}`. -/
theorem trFreshLaw_mul_exp_mul_chQ_le_of_mem_trAtoms {n : ℕ} {ξ : ResidueGroup n} {m : ℕ}
    (hm : 0 < m) {e : ℤ × ℤ} (he : e ∈ bkPoints) (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {g : ℕ}
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n) (hμa : trFreshLaw n e g a ≠ 0) :
    trFreshLaw n e g a * Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar - 1))) *
        chQ n ξ (epsStar : ℝ) (trFreshPath e a pStar) ≤
      (m : ℝ) ^ (-(Aexp : ℝ)) * ((m : ℝ) ^ (Aexp : ℝ) *
        (trBad n e m).indicator (fun _ ↦ trFreshLaw n e g a) a +
        (ccont : ℝ) * (trLow n ξ e \ trBad n e m).indicator (fun _ ↦ trFreshLaw n e g a) a +
        1 / (PW : ℝ) * trFreshLaw n e g a) * chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hA0 : (0 : ℝ) ≤ (Aexp : ℝ) := by exact_mod_cast Aexp_pos.le
  have hz0 : (0 : ℝ) ≤ (zStar : ℝ) := by exact_mod_cast zStar_nonneg
  have hMM : (m : ℝ) ^ (-(Aexp : ℝ)) * (m : ℝ) ^ (Aexp : ℝ) = 1 := by
    rw [Real.rpow_neg hmpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hmpos _).ne']
  have hw0 : (0 : ℝ) ≤ 1 / (PW : ℝ) := by
    have : (0 : ℝ) < PW := by exact_mod_cast PW_pos
    positivity
  have hr1 : 1 ≤ (a.1.1 : ℤ) := (firstPassageLaw_support (left_ne_zero_of_mul hμa)).1
  set y := trFreshPath e a pStar with hy_def
  have hadv : bkJ e + a.1.1 ≤ bkJ y := by
    have := trPath_fst_ge (bkJ e + a.1.1, bkL e + a.1.2) a.2 pStar
    simpa [hy_def, trFreshPath] using this
  set r : ℕ := (bkJ y - bkJ e).toNat with hr_def
  have hrZ : (r : ℤ) = bkJ y - bkJ e := Int.toNat_of_nonneg (by omega)
  have hbd := chQ_le_boundary_step n ξ (epsStar : ℝ) hA0 (m := m) (r := r) (by omega)
    (trFreshPath_mem_bkPoints he a pStar) (by rw [← hy_def]; omega)
  rw [← hy_def] at hbd
  set D : ℝ := ((max ((m : ℤ) - r) 1 : ℤ) : ℝ) with hD_def
  have hD1 : 1 ≤ D := by
    rw [hD_def]
    exact_mod_cast le_max_right _ _
  have hD0 : 0 < D := by linarith
  set E : ℝ := Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar - 1))) with hE_def
  have hN0 := trWhiteCount_nonneg (n := n) (ξ := ξ) e a (pStar - 1)
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hz0 hN0))
  have hη : a ∉ trLow n ξ e → E ≤ Real.exp (-(101 * (zStar : ℝ))) := by
    intro haL
    have h := lt_trWhiteCount_of_notMem_trLow ha haL
    rw [tStar_def, Nat.cast_ofNat] at h
    rw [hE_def, Real.exp_le_exp]
    nlinarith
  have hκ := c3Case3_atom_le (trBad n e m) (trLow n ξ e) a (trFreshLaw_nonneg n e g a)
    (Real.exp_pos _).le hE1 (Real.rpow_nonneg hD0.le _)
    (Real.rpow_le_one_of_one_le_of_nonpos hD1 (neg_nonpos.2 hA0)) (Real.rpow_nonneg hmpos.le _)
    hMM (fun hb ↦ rpow_neg_max_sub_le_of_notMem_trBad hm hA0 ha hb hrZ) rpow_Aexp_lt_ccont.le hη
    exp_neg_zStar_mul_rpow_Aexp_lt.le hw0
  calc trFreshLaw n e g a * E * chQ n ξ (epsStar : ℝ) y
      ≤ trFreshLaw n e g a * E * (D ^ (-(Aexp : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1)) :=
        mul_le_mul_of_nonneg_left hbd (mul_nonneg (trFreshLaw_nonneg n e g a) (Real.exp_pos _).le)
    _ = trFreshLaw n e g a * E * D ^ (-(Aexp : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hκ (chQm_nonneg _ _ _ _ _)

/-- In Case 3 the fresh law gives the low-white non-bad atoms `L \ B` mass less than
`X + 1 / P_T + 2^{-43}`. -/
theorem tsum_trLow_diff_trBad_trFreshLaw_lt {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {m : ℕ} (hmsc : (Dsc : ℝ) ≤ m) {e : ℤ × ℤ} (he : e ∈ bkPoints)
    (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {Δ : BkTriangle} (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ))
    (heΔ : e ∈ Δ) {g : ℕ} (hg : bkL e + g = Δ.l) (hgap : (m : ℝ) / Real.log m ^ 2 < g)
    (hPN : pStar ≤ n / 2) :
    ∑' a : ↥(trLow n ξ e \ trBad n e m), trFreshLaw n e g a <
      (2 + 272 * ((Hstar : ℝ) + 1) * Qpack) / Kstar + 1 / 3360 + 1 / (PT : ℝ) +
        (2 : ℝ) ^ (-43 : ℤ) := by
  set X : ℝ := (2 + 272 * ((Hstar : ℝ) + 1) * Qpack) / Kstar + 1 / 3360 with hX_def
  have hX0 : 0 ≤ X := by
    have : (0 : ℝ) < Qpack := by exact_mod_cast Qpack_pos
    positivity
  have hPT : (0 : ℝ) ≤ 1 / (PT : ℝ) := by
    have : (0 : ℝ) < PT := by exact_mod_cast PT_pos
    positivity
  have h : ∑' a : ↥(trLow n ξ e \ trBad n e m), ENNReal.ofReal (trFreshLaw n e g a) <
      ENNReal.ofReal (X + 1 / (PT : ℝ) + (2 : ℝ) ^ (-43 : ℤ)) :=
    calc _ ≤ ∑' a : trEStar n ξ e, ENNReal.ofReal (trFreshLaw n e g a) +
          ENNReal.ofReal (1 / (PT : ℝ)) + ENNReal.ofReal ((2 : ℝ) ^ (-43 : ℤ)) :=
          tsum_trLow_diff_trBad_trFreshLaw_le hξ he hje g hPN
      _ < ENNReal.ofReal X + ENNReal.ofReal (1 / (PT : ℝ)) +
          ENNReal.ofReal ((2 : ℝ) ^ (-43 : ℤ)) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top
          (ENNReal.add_lt_add_right ENNReal.ofReal_ne_top
            (tsum_trFreshLaw_trEStar_lt hξ hΔ heΔ hg hmsc hPN hgap))
      _ = _ := by
        rw [← ENNReal.ofReal_add hX0 hPT, ← ENNReal.ofReal_add (add_nonneg hX0 hPT)
          (by positivity)]
  have hs : Summable fun a : ↥(trLow n ξ e \ trBad n e m) ↦ trFreshLaw n e g a :=
    (ENNReal.summable_toReal (h.trans_le le_top).ne).congr
      fun a ↦ ENNReal.toReal_ofReal (trFreshLaw_nonneg n e g _)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg n e g _) hs] at h
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 h).1

/-- The Case 3 budget: bounds `s_B < 1/8000`, `s_L < X + 1/P_T + 2^{-43}` and `s_A ≤ 1` on the
three masses give `s_B + c s_L + s_A / P_W ≤ 1`. -/
theorem c3_budget_le_one {sB sL sA : ℝ} (hB : sB < 1 / 8000)
    (hL : sL < (2 + 272 * ((Hstar : ℝ) + 1) * Qpack) / Kstar + 1 / 3360 + 1 / (PT : ℝ) +
      (2 : ℝ) ^ (-43 : ℤ)) (hA : sA ≤ 1) :
    sB + (ccont : ℝ) * sL + 1 / (PW : ℝ) * sA ≤ 1 := by
  have hw0 : (0 : ℝ) ≤ 1 / (PW : ℝ) := by
    have : (0 : ℝ) < PW := by exact_mod_cast PW_pos
    positivity
  have hc : (ccont : ℝ) = 511 / 10 := ccont_cast
  have hBud : (Bud : ℝ) < 1 := by exact_mod_cast Bud_lt_one
  rw [Bud_cast] at hBud
  rw [show (2 : ℝ) ^ (-43 : ℤ) = 1 / 2 ^ 43 by norm_num] at hL
  have hcL := mul_le_mul_of_nonneg_left hL.le (by rw [hc]; norm_num : (0 : ℝ) ≤ ccont)
  have hwA := mul_le_mul_of_nonneg_left hA hw0
  rw [hc] at hcL hBud ⊢
  generalize (2 + 272 * ((Hstar : ℝ) + 1) * Qpack) / Kstar = Y at *
  rw [div_eq_mul_one_div (511 / 10 : ℝ) (PT : ℝ)] at hBud
  generalize (1 : ℝ) / PT = t at *
  generalize (1 : ℝ) / PW = u at *
  linarith

/-- The pointwise Case 3 bound: the continuation integrand on `𝒜_n` is at most
`m^{-A} (m^A μ 1_B + c μ 1_{L \ B} + μ 1_{𝒜_n} / P_W) Q_{m-1}`. -/
theorem trAtoms_indicator_le_rpow_mul_chQm {n : ℕ} {ξ : ResidueGroup n} {m : ℕ} (hm : 0 < m)
    {e : ℤ × ℤ} (he : e ∈ bkPoints) (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ)) (g : ℕ)
    (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    (trAtoms n).indicator (fun a ↦ trFreshLaw n e g a *
        Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar - 1))) *
        chQ n ξ (epsStar : ℝ) (trFreshPath e a pStar)) a ≤
      (m : ℝ) ^ (-(Aexp : ℝ)) * ((m : ℝ) ^ (Aexp : ℝ) *
        (trBad n e m).indicator (trFreshLaw n e g) a +
        (ccont : ℝ) * (trLow n ξ e \ trBad n e m).indicator (trFreshLaw n e g) a +
        1 / (PW : ℝ) * (trAtoms n).indicator (trFreshLaw n e g) a) *
        chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) := by
  have h1 := Set.indicator_nonneg (fun a _ ↦ trFreshLaw_nonneg n e g a) (s := trBad n e m) a
  have h2 := Set.indicator_nonneg (fun a _ ↦ trFreshLaw_nonneg n e g a)
    (s := trLow n ξ e \ trBad n e m) a
  have h3 := Set.indicator_nonneg (fun a _ ↦ trFreshLaw_nonneg n e g a) (s := trAtoms n) a
  have hQ := chQm_nonneg n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1)
  have hc : (0 : ℝ) ≤ ccont := by exact_mod_cast ccont_pos.le
  have hw : (0 : ℝ) < PW := by exact_mod_cast PW_pos
  by_cases ha : a ∈ trAtoms n
  swap
  · rw [Set.indicator_of_notMem ha]
    positivity
  rw [Set.indicator_of_mem ha]
  by_cases hμa : trFreshLaw n e g a = 0
  · rw [hμa, zero_mul, zero_mul]
    positivity
  refine (trFreshLaw_mul_exp_mul_chQ_le_of_mem_trAtoms hm he hje ha hμa).trans_eq ?_
  simp only [Set.indicator_of_mem ha]
  rfl

/-- In Case 3 the weighted fresh mass `m^A μ 1_B + c μ 1_{L \ B} + μ 1_{𝒜_n} / P_W` has total
mass at most `1`. -/
theorem exists_hasSum_c3_weight_le_one {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {m : ℕ} (hmsc : (Dsc : ℝ) ≤ m) (hmbad : (Dbad : ℝ) ≤ m) {e : ℤ × ℤ} (he : e ∈ bkPoints)
    (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {Δ : BkTriangle} (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ))
    (heΔ : e ∈ Δ) {g : ℕ} (hg : bkL e + g = Δ.l) (hgap : (m : ℝ) / Real.log m ^ 2 < g)
    (hPN : pStar ≤ n / 2) :
    ∃ s ≤ 1, HasSum (fun a ↦ (m : ℝ) ^ (Aexp : ℝ) * (trBad n e m).indicator (trFreshLaw n e g) a +
      (ccont : ℝ) * (trLow n ξ e \ trBad n e m).indicator (trFreshLaw n e g) a +
      1 / (PW : ℝ) * (trAtoms n).indicator (trFreshLaw n e g) a) s := by
  set μ := trFreshLaw n e g
  set S := trAtoms n
  set B := trBad n e m
  set L := trLow n ξ e
  have hμ0 : ∀ a, 0 ≤ μ a := trFreshLaw_nonneg n e g
  have hSμE := chQ_le_rpow_mul_chQm_of_gap_gt_tsum_le_one n e g
  have hSμsub : Summable fun a : S ↦ μ a :=
    (ENNReal.summable_toReal (hSμE.trans_lt ENNReal.one_lt_top).ne).congr
      fun a ↦ ENNReal.toReal_ofReal (hμ0 _)
  have hSμ : Summable (S.indicator μ) := (summable_subtype_iff_indicator).1 hSμsub
  have hsubμ : ∀ {s : Set ((ℕ × ℤ) × List (List ℤ × ℤ))}, s ⊆ S → Summable (s.indicator μ) :=
    fun hs ↦ Summable.of_nonneg_of_le (Set.indicator_nonneg fun a _ ↦ hμ0 a)
      (Set.indicator_le_indicator_of_subset hs fun a ↦ hμ0 a) hSμ
  have hBμ := hsubμ (s := B) (trBad_subset_trAtoms n e m)
  have hLBμ := hsubμ (s := L \ B) fun a ha ↦ trLow_subset_trAtoms n ξ e ha.1
  have hBad : (m : ℝ) ^ (Aexp : ℝ) * ∑' a, B.indicator μ a < 1 / 8000 := by
    rw [← tsum_subtype]
    exact c3_bad_mass e hmbad hPN
      (chQ_le_rpow_mul_chQm_of_gap_gt_natCast_mul_log_two_le hξ hje hΔ heΔ hg)
  have hLow : ∑' a, (L \ B).indicator μ a < _ := (tsum_subtype (L \ B) μ).symm.trans_lt
    (tsum_trLow_diff_trBad_trFreshLaw_lt hξ hmsc he hje hΔ heΔ hg hgap hPN)
  have hAll : ∑' a, S.indicator μ a ≤ 1 := by
    rw [← tsum_subtype]
    have hSeq : ∑' a : S, ENNReal.ofReal (μ a) = ENNReal.ofReal (∑' a : S, μ a) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ hμ0 _) hSμsub).symm
    exact ENNReal.ofReal_le_one.1 (hSeq ▸ hSμE)
  exact ⟨_, c3_budget_le_one hBad hLow hAll,
    ((hBμ.hasSum.mul_left _).add (hLBμ.hasSum.mul_left _)).add (hSμ.hasSum.mul_left _)⟩

/-- **Case 3 of the monotonicity step.** Let `ξ` be a unit and
`m ∈ ℕ` with `m ≥ D_sc` and `m ≥ D_bad`. Let `e ∈ Δ` for some `Δ ∈ 𝔗_{n,ξ,ε_*}` with
`j(e) + m = ⌊n/2⌋` and `l_Δ - l(e) > m / (log m)^2`. Then `Q(e) ≤ m^{-A_*} Q_{m-1}`, where
`Q` and `Q_{m-1}` are formed with `ε = ε_*` and `A = A_*`. -/
@[collatz_pos_dens "lem_c3_case3"]
theorem chQ_le_rpow_mul_chQm_of_gap_gt {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {m : ℕ} (hmsc : (Dsc : ℝ) ≤ m) (hmbad : (Dbad : ℝ) ≤ m)
    {e : ℤ × ℤ} (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {Δ : BkTriangle}
    (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ)) (heΔ : e ∈ Δ)
    (hgap : (m : ℝ) / Real.log m ^ 2 < ((Δ.l - bkL e : ℤ) : ℝ)) :
    chQ n ξ (epsStar : ℝ) e ≤
      (m : ℝ) ^ (-(Aexp : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) := by
  have he : e ∈ bkPoints := BkTriangle.mem_bkPoints_of_mem heΔ
  obtain ⟨g, hg⟩ : ∃ g : ℕ, bkL e + g = Δ.l :=
    ⟨(Δ.l - bkL e).toNat, by have := heΔ.2.1; omega⟩
  rw [← hg, add_sub_cancel_left, Int.cast_natCast] at hgap
  have hPN : pStar ≤ n / 2 := by
    have := mem_bkPoints.1 he
    have : pStar ≤ m := by exact_mod_cast pStar_le_of_Dsc_le hmsc
    omega
  have hm1 : 1 ≤ m := by
    have : Dsc ≤ m := by exact_mod_cast hmsc
    have := two_le_Dsc
    omega
  obtain ⟨s, hs1, hR⟩ := exists_hasSum_c3_weight_le_one hξ hmsc hmbad he hje hΔ heΔ hg hgap hPN
  set Mi : ℝ := (m : ℝ) ^ (-(Aexp : ℝ))
  set Qm := chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1)
  set T : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ := fun a ↦ trFreshLaw n e g a *
    Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar - 1))) *
    chQ n ξ (epsStar : ℝ) (trFreshPath e a pStar)
  have hRsum := (hR.mul_left Mi).mul_right Qm
  have hpt := trAtoms_indicator_le_rpow_mul_chQm (ξ := ξ) hm1 he hje g
  have hTsum : Summable ((trAtoms n).indicator T) :=
    Summable.of_nonneg_of_le
      (Set.indicator_nonneg fun a _ ↦ mul_nonneg
        (mul_nonneg (trFreshLaw_nonneg n e g a) (Real.exp_pos _).le) (chQ_nonneg _ _ _ _))
      hpt hRsum.summable
  calc chQ n ξ (epsStar : ℝ) e ≤ ∑' a : trAtoms n, T a :=
        chQ_le_tsum_trFreshLaw_mul_exp n ξ he g hPN
    _ = ∑' a, (trAtoms n).indicator T a := tsum_subtype _ T
    _ ≤ _ := hTsum.tsum_le_tsum hpt hRsum.summable
    _ = Mi * s * Qm := hRsum.tsum_eq
    _ ≤ Mi * 1 * Qm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (chQm_nonneg _ _ _ _ _)
    _ = Mi * Qm := by ring

end CollatzPosDens
