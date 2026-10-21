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
public import CollatzPosDens.BlackSet.BkCover
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkRightEdge
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.CharSum.ChBoundaryStep
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Dbad
public import CollatzPosDens.Transfer.S02Dsc
public import CollatzPosDens.Transfer.S02FarB
public import CollatzPosDens.Transfer.S02FarS
public import CollatzPosDens.Transfer.S02OmegaLower
public import CollatzPosDens.Transfer.S02PW
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Qmass
public import CollatzPosDens.Transfer.S02PiAd
public import CollatzPosDens.Transfer.S02Eta
public import CollatzPosDens.Transfer.S02Split
public import CollatzPosDens.Transfer.S02WeightedSqrt
public import CollatzPosDens.Transfer.S02Uo
public import CollatzPosDens.Transfer.S02Uv
public import CollatzPosDens.Transfer.S02Ud
public import CollatzPosDens.Transfer.S02EpsInit
public import CollatzPosDens.Transfer.S02Epiece
public import CollatzPosDens.Transfer.S02Budget
public import CollatzPosDens.Transfer.S02BudgetLem
public import CollatzPosDens.Transfer.S02Cont
public import CollatzPosDens.Transfer.S02ContLem
public import CollatzPosDens.Transfer.S02WhiteTerm
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass
public import CollatzPosDens.StoppingTrace.TrWhiteCount
public import CollatzPosDens.Case3.C3BadMass
public import CollatzPosDens.Case3.C3Continuation
public import CollatzPosDens.Case3.C3EstarMass
public import CollatzPosDens.Case3.C3GapRatio
public import CollatzPosDens.Case3.C3GapTop
public import CollatzPosDens.Case3.C3InitialMass
public import CollatzPosDens.Case3.C3PaidDom
public import CollatzPosDens.Case3.C3PaidLaw

/-!
# The bound on `Q(e)` above the split level

Let `ι` be a Fourier index, `ξ` a unit, `m` an integer with `m ≥ D_sc(ι)`, `m ≥ D_bad(ι)` and
`m ≤ J = ⌊n/2⌋`, and `e ∈ 𝒫` with `j(e) + m = J`. Suppose `e ∈ Δ` for a triangle
`Δ ∈ 𝔗_{n,ξ,ε_*}` and that the gap `ω = gap(e)` exceeds the split level, `ω > ς(ι, m)`. Then
$$\mathsf Q(e) \le m^{-A_*(\iota)}\,\mathsf Q_{m-1},$$
both sides formed with `ε = ε_*` and `A = A_*(ι)`. Throughout the proof `ι` is fixed and every
recipe constant (`A_*`, `P_*`, `T_*`, `c_cont`, `P_W`, the budget terms, `Bud`) is taken at `ι`.

The point `e` is black and `l_Δ - l(e) = ω`, so `ω log 2 ≤ m log 9` by the right edge of `Δ`.
The continuation through the paid passage (at `L = P_*`) bounds `Q(e)` by the sum, over the
paid fresh law `μ̃_e`, of `e^{-z_* N(a)} Q(y^e_{P_*}(a))`, `N(a)` the weighted white count up to
time `P_* - 1`. On an atom of positive mass the advance `Adv(a) = j(y^e_{P_*}(a)) - j(e)` is at
least `1`, so the boundary step bounds `Q(y^e_{P_*}(a))` by `max(m - Adv(a), 1)^{-A_*} Q_{m-1}`.
Off `Bad^e_m` this is at most `(400/83)^{A_*} m^{-A_*} Q_{m-1} < c_cont m^{-A_*} Q_{m-1}`, and
off `Low^e` moreover `e^{-z_* N(a)} (400/83)^{A_*} < e^{-z_* T_*} (400/83)^{A_*} < 1/P_W = w`.
Hence the integrand is at most `m^{-A_*} Q_{m-1}` times
`m^{A_*} 1_{Bad} + (c_cont - w) e^{-z_* N} 1_{Low \ Bad} + w`. Summing, the three masses are
controlled by the outer horizontal tail (through the domination `μ̃_e ≤ μ_{e,ω}`), by the
discounted mass of `Low^e \ Bad^e_m` (at most
`Π_ad + q_mass η_{r_*} + 𝓔_sq + U_o + ε_init + q_mass (U_v + U_d + E_piece)`), and by the
initial paid mass `< q_mass` (valid as `ω > ς(ι, m) ≥ Ω_far ≥ 2^34`); the bracket is then at most
the budget `Bud < 1`.

## Main results

* `CollatzPosDens.chQ_le_rpow_mul_chQm_of_gap_gt`: if `gap(e) > ς(ι, m)`, then
  `Q(e) ≤ m^{-A_*(ι)} Q_{m-1}`.
* `CollatzPosDens.natCast_trGap_toNat_mul_log_two_le`: the gap satisfies `ω log 2 ≤ m log 9`.
* `CollatzPosDens.c3PaidLaw_mul_ofReal_exp_mul_chQ_le`: the pointwise bound on a fresh atom.
* `CollatzPosDens.tsum_trAtoms_c3PaidLaw_le`: the paid fresh law of `𝒜_n` is at most the total
  paid passage mass.

## Implementation notes

The hypotheses `n ≥ 1`, `e ∈ 𝒫` and `m ≤ ⌊n/2⌋` are not assumed: `e ∈ 𝒫` follows from
`e ∈ Δ`, and then `m ≤ ⌊n/2⌋` (hence `n ≥ 1`) follows from `j(e) + m = ⌊n/2⌋`. The integer
`m ≥ D_sc(ι) ≥ 2` is taken in `ℕ`, and `m^{-A_*(ι)}` is the real power `(m : ℝ) ^ (-A_*(ι))`.
The paid fresh law is `[0, ∞]`-valued, so the summation is carried out in `[0, ∞]`, where it
needs no summability side conditions.

## References

* [Mazur, *Collatz positive density*], §10.6.
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

open Real

/-- If `e ∈ Δ ∈ 𝔗_{n,ξ,ε_*}` with `j(e) + m = ⌊n/2⌋` and `l(e) + g = l_Δ`, then
`g log 2 ≤ m log 9`. -/
theorem natCast_mul_log_two_le_of_add_eq {n : ℕ}
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

/-- **Gap versus distance.** If `e ∈ Δ ∈ 𝔗_{n,ξ,ε_*}` with `j(e) + m = ⌊n/2⌋`, then the gap
`ω = gap(e)` satisfies `ω log 2 ≤ m log 9`. -/
theorem natCast_trGap_toNat_mul_log_two_le {n : ℕ}
    {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {m : ℕ} {e : ℤ × ℤ}
    (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {Δ : BkTriangle}
    (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ)) (heΔ : e ∈ Δ) :
    ((trGap n ξ (epsStar : ℝ) e).toNat : ℝ) * log 2 ≤ m * log 9 :=
  natCast_mul_log_two_le_of_add_eq hξ hje hΔ heΔ (by
    rw [Int.toNat_of_nonneg (trGap_nonneg _ _ _ _)]
    exact (bkFamily_epsStar_l_eq_add_trGap hξ hΔ heΔ).symm)

/-- If `κ m ≤ D` with `κ, m > 0` and `A ≥ 0`, then `D ^ (-A) ≤ κ⁻¹ ^ A * m ^ (-A)`. -/
theorem rpow_neg_le_inv_rpow_mul_rpow_neg {m D A κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hA : 0 ≤ A)
    (h : κ * m ≤ D) : D ^ (-A) ≤ κ⁻¹ ^ A * m ^ (-A) := by
  calc D ^ (-A) ≤ (κ * m) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hκ hm) h (neg_nonpos.2 hA)
    _ = κ⁻¹ ^ A * m ^ (-A) := by
        rw [Real.mul_rpow hκ.le hm.le, Real.rpow_neg hκ.le, ← Real.inv_rpow hκ.le]

/-- Off the bad atoms, the boundary weight `max(m - r, 1)^{-A}` is at most `(400/83)^A m^{-A}`,
where `r` is the advance of the fresh path. -/
theorem rpow_neg_max_sub_le_of_notMem_trBad {ι : FIndex} {n : ℕ} {e : ℤ × ℤ} {m : ℕ}
    (hm : 0 < m) {A : ℝ} (hA : 0 ≤ A) {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n)
    (hb : a ∉ trBad ι n e m)
    {r : ℕ} (hr : (r : ℤ) = bkJ (trFreshPath e a (pStar ι)) - bkJ e) :
    ((max ((m : ℤ) - r) 1 : ℤ) : ℝ) ^ (-A) ≤ (400 / 83 : ℝ) ^ A * (m : ℝ) ^ (-A) := by
  have h := lt_of_not_mem_trBad ha hb
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

/-- **The atom bound of Case 3.** Let `e ∈ 𝒫`, `m ≥ 1` with `j(e) + m = ⌊n/2⌋`, and `a ∈ 𝒜_n`.
With `E(a) = e^{-z_* N^e_{P_*-1}(a)}` and `w = 1/P_W`, the contribution
`μ̃_e(a) E(a) Q(y^e_{P_*}(a))` of `a` to the continuation sum is at most
`m^{-A_*} Q_{m-1} (m^{A_*} μ̃_e(a) 1_{Bad^e_m}(a)
  + (c_cont - w) μ̃_e(a) E(a) 1_{Low^e \ Bad^e_m}(a) + w μ̃_e(a))`. -/
theorem c3PaidLaw_mul_ofReal_exp_mul_chQ_le (ι : FIndex) {n : ℕ} {ξ : ResidueGroup n} {m : ℕ}
    (hm : 0 < m) {e : ℤ × ℤ} (he : e ∈ bkPoints) (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ))
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n) :
    c3PaidLaw n ξ e a *
        ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1))) *
          chQ n ξ (epsStar : ℝ) (trFreshPath e a (pStar ι))) ≤
      ENNReal.ofReal ((m : ℝ) ^ (-(Aexp ι : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp ι : ℝ) (m - 1)) *
        (ENNReal.ofReal ((m : ℝ) ^ (Aexp ι : ℝ)) * (trBad ι n e m).indicator (c3PaidLaw n ξ e) a +
          ENNReal.ofReal ((ccont ι : ℝ) - 1 / (PW ι : ℝ)) *
            (trLow ι n ξ e \ trBad ι n e m).indicator (fun a ↦ c3PaidLaw n ξ e a *
              ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1))))) a +
          ENNReal.ofReal (1 / (PW ι : ℝ)) * c3PaidLaw n ξ e a) := by
  set μa := c3PaidLaw n ξ e a with hμa_def
  by_cases hμa : μa = 0
  · rw [hμa, zero_mul]
    exact zero_le
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hA0 : (0 : ℝ) ≤ (Aexp ι : ℝ) := by exact_mod_cast (Aexp_pos ι).le
  have hz0 : (0 : ℝ) ≤ (zStar : ℝ) := by exact_mod_cast zStar_nonneg
  have hPW : (0 : ℝ) < PW ι := by exact_mod_cast (PW_pos ι)
  have hw0 : (0 : ℝ) ≤ 1 / (PW ι : ℝ) := by positivity
  have hw1 : 1 / (PW ι : ℝ) ≤ 1 := by
    rw [div_le_one hPW]
    exact_mod_cast (one_le_PW ι)
  have hc1 : (1 : ℝ) < ccont ι := by exact_mod_cast (one_lt_ccont ι)
  -- the advance is at least `1`
  have hr1 : 1 ≤ (a.1.1 : ℤ) := by
    by_contra h
    apply hμa
    rw [hμa_def, c3PaidLaw_def, c3PaidPassage_eq_zero_of_fst_lt_one (by simpa using h),
      zero_mul]
  set y := trFreshPath e a (pStar ι) with hy_def
  have hadv : bkJ e + a.1.1 ≤ bkJ y := by
    have := trPath_fst_ge (bkJ e + a.1.1, bkL e + a.1.2) a.2 (pStar ι)
    simpa [hy_def, trFreshPath] using this
  set r : ℕ := (bkJ y - bkJ e).toNat with hr_def
  have hrZ : (r : ℤ) = bkJ y - bkJ e := Int.toNat_of_nonneg (by omega)
  have hbd := chQ_le_boundary_step n ξ (epsStar : ℝ) hA0 (m := m) (r := r) (by omega)
    (trFreshPath_mem_bkPoints he a (pStar ι)) (by rw [← hy_def]; omega)
  rw [← hy_def] at hbd
  set D : ℝ := ((max ((m : ℤ) - r) 1 : ℤ) : ℝ) with hD_def
  have hD1 : 1 ≤ D := by
    rw [hD_def]
    exact_mod_cast le_max_right _ _
  set K : ℝ := D ^ (-(Aexp ι : ℝ)) with hK_def
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by linarith) _
  have hK1 : K ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hD1 (neg_nonpos.2 hA0)
  set Qm := chQm n ξ (epsStar : ℝ) (Aexp ι : ℝ) (m - 1) with hQm_def
  have hQm : 0 ≤ Qm := chQm_nonneg _ _ _ _ _
  set M : ℝ := (m : ℝ) ^ (-(Aexp ι : ℝ)) with hM_def
  have hM0 : 0 ≤ M := Real.rpow_nonneg hmpos.le _
  have hMM : M * (m : ℝ) ^ (Aexp ι : ℝ) = 1 := by
    rw [hM_def, Real.rpow_neg hmpos.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hmpos _).ne']
  set E : ℝ := Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1))) with hE_def
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2
    (neg_nonpos.2 (mul_nonneg hz0 (trWhiteCount_nonneg _ _ _)))
  have hQy : chQ n ξ (epsStar : ℝ) y ≤ K * Qm := hbd
  have hQy0 : 0 ≤ chQ n ξ (epsStar : ℝ) y := chQ_nonneg _ _ _ _
  have hEQ : E * chQ n ξ (epsStar : ℝ) y ≤ E * (K * Qm) := mul_le_mul_of_nonneg_left hQy hE0
  set R := ENNReal.ofReal (M * Qm) with hR_def
  -- reduce to a bound `E Q(y) ≤ x` and `μ̃(a) ofReal x ≤ RHS`
  suffices h : ∃ x : ℝ, E * chQ n ξ (epsStar : ℝ) y ≤ x ∧ μa * ENNReal.ofReal x ≤
      R * (ENNReal.ofReal ((m : ℝ) ^ (Aexp ι : ℝ)) * (trBad ι n e m).indicator (c3PaidLaw n ξ e) a +
          ENNReal.ofReal ((ccont ι : ℝ) - 1 / (PW ι : ℝ)) *
            (trLow ι n ξ e \ trBad ι n e m).indicator (fun a ↦ c3PaidLaw n ξ e a *
              ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1))))) a +
          ENNReal.ofReal (1 / (PW ι : ℝ)) * μa) by
    obtain ⟨x, hx, hx'⟩ := h
    exact (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hx) zero_le).trans hx'
  by_cases haB : a ∈ trBad ι n e m
  · refine ⟨Qm, ?_, ?_⟩
    · exact hEQ.trans (by nlinarith)
    · rw [Set.indicator_of_mem haB]
      calc μa * ENNReal.ofReal Qm = R * (ENNReal.ofReal ((m : ℝ) ^ (Aexp ι : ℝ)) * μa) := by
            rw [hR_def, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hM0 hQm),
              mul_comm, mul_right_comm M, hMM, one_mul]
        _ ≤ _ := by gcongr; exact le_self_add.trans le_self_add
  have hKb : K ≤ (400 / 83 : ℝ) ^ (Aexp ι : ℝ) * M :=
    rpow_neg_max_sub_le_of_notMem_trBad hm hA0 ha haB (by rw [hrZ])
  have hcont : (400 / 83 : ℝ) ^ (Aexp ι : ℝ) < ccont ι := (rpow_Aexp_lt_ccont ι)
  rw [Set.indicator_of_notMem haB, mul_zero, zero_add]
  by_cases haL : a ∈ trLow ι n ξ e
  · refine ⟨M * Qm * (((ccont ι : ℝ) - 1 / PW ι) * E + 1 / PW ι), ?_, ?_⟩
    · have hKc : K ≤ ccont ι * M := hKb.trans (mul_le_mul_of_nonneg_right hcont.le hM0)
      have : E * (K * Qm) ≤ E * (ccont ι * M * Qm) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKc hQm) hE0
      have h2 : E * (ccont ι * M * Qm) ≤ M * Qm * (((ccont ι : ℝ) - 1 / PW ι) * E + 1 / PW ι) := by
        have : 0 ≤ M * Qm * (1 / PW ι * (1 - E)) :=
          mul_nonneg (mul_nonneg hM0 hQm) (mul_nonneg hw0 (by linarith))
        nlinarith
      linarith
    · rw [Set.indicator_of_mem (show a ∈ trLow ι n ξ e \ trBad ι n e m from ⟨haL, haB⟩)]
      rw [ENNReal.ofReal_mul (mul_nonneg hM0 hQm), ← hR_def, ENNReal.ofReal_add
        (mul_nonneg (by linarith) hE0) hw0, ENNReal.ofReal_mul (by linarith)]
      apply le_of_eq
      ring
  · refine ⟨M * Qm * (1 / PW ι), ?_, ?_⟩
    · have hN := lt_trWhiteCount_of_notMem_trLow ha haL
      have hEle : E ≤ Real.exp (-((zStar : ℝ) * tStar ι)) := by
        rw [hE_def, Real.exp_le_exp]
        nlinarith
      have hwt := (exp_neg_zStar_mul_rpow_Aexp_lt ι)
      have : E * K ≤ Real.exp (-((zStar : ℝ) * tStar ι)) * ((400 / 83 : ℝ) ^ (Aexp ι : ℝ) * M) :=
        mul_le_mul hEle hKb hK0 (Real.exp_pos _).le
      have h3 : E * K ≤ 1 / PW ι * M := this.trans (by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hwt.le hM0)
      calc E * chQ n ξ (epsStar : ℝ) y ≤ E * K * Qm := by rw [mul_assoc]; exact hEQ
        _ ≤ 1 / PW ι * M * Qm := mul_le_mul_of_nonneg_right h3 hQm
        _ = M * Qm * (1 / PW ι) := by ring
    · rw [Set.indicator_of_notMem (fun h ↦ haL h.1), mul_zero, zero_add,
        ENNReal.ofReal_mul (mul_nonneg hM0 hQm), ← hR_def]
      apply le_of_eq
      ring

/-- The paid fresh law of the fresh atoms is at most the total paid passage mass:
`μ̃_e(𝒜_n) ≤ ∑_{x ∈ ℤ × ℤ} F̃_e(x)`, since the block lists of `𝔅^{⌊n/2⌋}` have total weight `1`. -/
theorem tsum_trAtoms_c3PaidLaw_le (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) :
    ∑' a : trAtoms n, c3PaidLaw n ξ e a ≤ ∑' x : ℤ × ℤ, c3PaidPassage n ξ e x := by
  rw [← (trAtomsEquiv n).symm.tsum_eq, ENNReal.tsum_prod']
  calc _ = ∑' y : ℕ × ℤ, c3PaidPassage n ξ e ((y.1 : ℤ), y.2) := by
        refine tsum_congr fun y ↦ ?_
        simp only [trAtomsEquiv, Equiv.coe_fn_symm_mk, c3PaidLaw_def]
        rw [ENNReal.tsum_mul_left, tsum_ofReal_trListWeight_length_eq, mul_one]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun y : ℕ × ℤ ↦ ((y.1 : ℤ), y.2))
        (fun y y' h ↦ by
          simp only [Prod.mk.injEq, Nat.cast_inj] at h
          exact Prod.ext h.1 h.2) _

/-- A sum over `𝒜_n` of an indicator of `s` is at most the sum over `s`. -/
theorem tsum_trAtoms_indicator_le (n : ℕ) (s : Set ((ℕ × ℤ) × List (List ℤ × ℤ)))
    (f : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞) :
    ∑' a : trAtoms n, s.indicator f a ≤ ∑' a : s, f a := by
  rw [tsum_subtype s f]
  exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _

/-- **Bad atoms under the paid law.** With `ω = gap(e)` and `m ≥ D_bad`, `P_* ≤ ⌊n/2⌋` and
`ω log 2 ≤ m log 9`, the paid fresh law of `Bad^e_m` satisfies `m^{A_*} μ̃_e(Bad^e_m) ≤ 1/8000`. -/
theorem ofReal_rpow_mul_tsum_trBad_c3PaidLaw_le (ι : FIndex) {n : ℕ} {ξ : ResidueGroup n}
    {e : ℤ × ℤ} {m : ℕ} (hm : (Dbad ι : ℝ) ≤ m) (hP : pStar ι ≤ n / 2)
    (hω : ((trGap n ξ (epsStar : ℝ) e).toNat : ℝ) * log 2 ≤ m * log 9) :
    ENNReal.ofReal ((m : ℝ) ^ (Aexp ι : ℝ)) * ∑' a : trBad ι n e m, c3PaidLaw n ξ e a ≤
      ENNReal.ofReal (1 / 8000) := by
  set G := (trGap n ξ (epsStar : ℝ) e).toNat
  have hm1 : 1 ≤ m := by
    have h' : (2 : ℝ) ^ 43 ≤ (Dbad ι : ℝ) := by exact_mod_cast two_pow_43_le_Dbad ι
    exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  have hGm : (G : ℝ) ≤ 158497 / 50000 * m := by
    have h2 : 0 < log 2 := log_pos (by norm_num)
    have h9 : log 9 < 158497 / 50000 * log 2 := (div_lt_iff₀ h2).1 log_nine_div_log_two_lt
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hs := c3_bad_mass_summable ι e hm1 hP hGm
  have hdom : ∑' a : trBad ι n e m, c3PaidLaw n ξ e a ≤
      ENNReal.ofReal (∑' a : trBad ι n e m, trFreshLaw n e G a) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _) hs]
    exact ENNReal.tsum_le_tsum fun a ↦
      c3PaidLaw_le_ofReal_trFreshLaw (trGap_nonneg _ _ _ _) a
  calc _ ≤ ENNReal.ofReal ((m : ℝ) ^ (Aexp ι : ℝ)) *
        ENNReal.ofReal (∑' a : trBad ι n e m, trFreshLaw n e G a) := by gcongr
    _ = ENNReal.ofReal ((m : ℝ) ^ (Aexp ι : ℝ) * ∑' a : trBad ι n e m, trFreshLaw n e G a) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (c3_bad_mass ι e hm hP hω).le

/-- **The Case 3 budget**, in `[0, ∞]`: masses `b ≤ 1/8000`,
`X ≤ Π_ad + q_mass η_{r_*} + 𝓔_sq + U_o + ε_init + q_mass (U_v + U_d + E_piece)` and
`t ≤ q_mass` give `b + (c_cont - 1/P_W) X + t / P_W ≤ Bud(ι) ≤ 1`. -/
theorem c3_budget_le_one (ι : FIndex) {b X t : ℝ≥0∞} (hb : b ≤ ENNReal.ofReal (1 / 8000))
    (hX : X ≤ ENNReal.ofReal ((piAd ι : ℝ) + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι +
      epsInit ι + qMass * ((Uv ι : ℝ) + Ud ι + ePiece ι)))
    (ht : t ≤ ENNReal.ofReal (qMass : ℝ)) :
    b + ENNReal.ofReal ((ccont ι : ℝ) - 1 / (PW ι : ℝ)) * X + ENNReal.ofReal (1 / (PW ι : ℝ)) * t ≤
      1 := by
  have hPW : (0 : ℝ) < PW ι := by exact_mod_cast (PW_pos ι)
  have hcw : (0 : ℝ) ≤ (ccont ι : ℝ) - 1 / (PW ι : ℝ) := by
    exact_mod_cast (ccont_sub_inv_PW_pos ι).le
  have hY : (0 : ℝ) ≤ (piAd ι : ℝ) + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι + epsInit ι +
      qMass * ((Uv ι : ℝ) + Ud ι + ePiece ι) := by
    have h1 : (0 : ℝ) < piAd ι := by exact_mod_cast (piAd_pos ι)
    have h2 : (0 : ℝ) < qMass := by exact_mod_cast qMass_pos
    have h3 : (0 : ℝ) < eventCoeff ι (rStar ι) := by exact_mod_cast eventCoeff_pos ι (rStar ι)
    have h4 : (0 : ℝ) < Esq ι := by exact_mod_cast (Esq_pos ι)
    have h5 : (0 : ℝ) < Uo ι := by exact_mod_cast (Uo_pos ι)
    have h6 : (0 : ℝ) < epsInit ι := by exact_mod_cast (epsInit_pos ι)
    have h7 : (0 : ℝ) < Uv ι := by exact_mod_cast (Uv_pos ι)
    have h8 : (0 : ℝ) < Ud ι := by exact_mod_cast (Ud_pos ι)
    have h9 : (0 : ℝ) ≤ ePiece ι := by exact_mod_cast (ePiece_nonneg ι)
    positivity
  have hq : (0 : ℝ) ≤ qMass := by exact_mod_cast qMass_pos.le
  calc _ ≤ ENNReal.ofReal (1 / 8000) + ENNReal.ofReal ((ccont ι : ℝ) - 1 / (PW ι : ℝ)) *
        ENNReal.ofReal ((piAd ι : ℝ) + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι + epsInit ι +
          qMass * ((Uv ι : ℝ) + Ud ι + ePiece ι)) +
          ENNReal.ofReal (1 / (PW ι : ℝ)) * ENNReal.ofReal (qMass : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (Bud ι : ℝ) := by
        rw [← ENNReal.ofReal_mul hcw, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by norm_num) (mul_nonneg hcw hY),
          ← ENNReal.ofReal_add (by positivity) (by positivity), Bud_cast]
        congr 1
        norm_num
        ring
    _ ≤ 1 := ENNReal.ofReal_le_one.2 (by exact_mod_cast (Bud_lt_one ι).le)

/-- Let `ι` be a Fourier index, `ξ` a unit and `m ∈ ℕ` with `m ≥ D_sc(ι)` and `m ≥ D_bad(ι)`.
Let `e ∈ Δ` for some `Δ ∈ 𝔗_{n,ξ,ε_*}` with `j(e) + m = ⌊n/2⌋` and `gap(e) > ς(ι, m)`, the split
level. Then `Q(e) ≤ m^{-A_*(ι)} Q_{m-1}`, where `Q` and `Q_{m-1}` are formed with `ε = ε_*` and
`A = A_*(ι)`. -/
@[collatz_pos_dens "lem_c3_case3"]
theorem chQ_le_rpow_mul_chQm_of_gap_gt (ι : FIndex) {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {m : ℕ} (hmsc : (Dsc ι : ℝ) ≤ m) (hmbad : (Dbad ι : ℝ) ≤ m)
    {e : ℤ × ℤ} (hje : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {Δ : BkTriangle}
    (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ)) (heΔ : e ∈ Δ)
    (hgap : gapSplit ι m < trGap n ξ (epsStar : ℝ) e) :
    chQ n ξ (epsStar : ℝ) e ≤
      (m : ℝ) ^ (-(Aexp ι : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp ι : ℝ) (m - 1) := by
  have he : e ∈ bkPoints := BkTriangle.mem_bkPoints_of_mem heΔ
  have hblack : BkBlack n ξ (epsStar : ℝ) e :=
    (bkBlack_iff_exists_mem_bkFamily hξ epsStar_mem_bkRange.1 epsStar_mem_bkRange.2 he).2
      ⟨Δ, hΔ, heΔ⟩
  have hPm : pStar ι ≤ m := by exact_mod_cast pStar_le_of_Dsc_le ι hmsc
  have hPN : pStar ι ≤ n / 2 := by
    have := mem_bkPoints.1 he
    omega
  have hm1 : 1 ≤ m := by
    have : Dsc ι ≤ m := by exact_mod_cast hmsc
    have := (two_le_Dsc ι)
    omega
  -- the gap is at least `2^34`
  have hω : (2 ^ 34 : ℤ) ≤ trGap n ξ (epsStar : ℝ) e := by
    have hFar : (omegaFar ι : ℝ) < trGap n ξ (epsStar : ℝ) e :=
      (omegaFar_le_gapSplit_of_Dsc_le ι hmsc).trans_lt hgap
    have h1 : ((2 ^ 34 : ℕ) : ℝ) ≤ omegaFar ι := by
      exact_mod_cast le_of_max_le_left (le_of_max_le_left (max_le_omegaFar ι))
    have h2 : ((2 ^ 34 : ℤ) : ℝ) = ((2 ^ 34 : ℕ) : ℝ) := by norm_num
    have : ((2 ^ 34 : ℤ) : ℝ) < trGap n ξ (epsStar : ℝ) e := by rw [h2]; linarith
    exact_mod_cast this.le
  set M := (m : ℝ) ^ (-(Aexp ι : ℝ))
  set Qm := chQm n ξ (epsStar : ℝ) (Aexp ι : ℝ) (m - 1)
  have hMQ : 0 ≤ M * Qm := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (chQm_nonneg _ _ _ _ _)
  set B := trBad ι n e m
  set LB := trLow ι n ξ e \ trBad ι n e m
  set μ := c3PaidLaw n ξ e
  set E : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦
    ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1))))
  rw [← ENNReal.ofReal_le_ofReal_iff hMQ]
  calc ENNReal.ofReal (chQ n ξ (epsStar : ℝ) e)
      ≤ ∑' a : trAtoms n, ENNReal.ofReal (M * Qm) *
          (ENNReal.ofReal ((m : ℝ) ^ (Aexp ι : ℝ)) * B.indicator μ a +
            ENNReal.ofReal ((ccont ι : ℝ) - 1 / (PW ι : ℝ)) * LB.indicator (fun a ↦ μ a * E a) a +
            ENNReal.ofReal (1 / (PW ι : ℝ)) * μ a) :=
        (chQ_le_tsum_trFreshLaw_mul_exp n ξ he hblack (one_le_pStar ι) hPN).trans_eq
          (by simp only [neg_mul]) |>.trans (ENNReal.tsum_le_tsum fun a ↦
          c3PaidLaw_mul_ofReal_exp_mul_chQ_le ι hm1 he hje a.2)
    _ = ENNReal.ofReal (M * Qm) *
          (ENNReal.ofReal ((m : ℝ) ^ (Aexp ι : ℝ)) * ∑' a : trAtoms n, B.indicator μ a +
            ENNReal.ofReal ((ccont ι : ℝ) - 1 / (PW ι : ℝ)) *
              ∑' a : trAtoms n, LB.indicator (fun a ↦ μ a * E a) a +
            ENNReal.ofReal (1 / (PW ι : ℝ)) * ∑' a : trAtoms n, μ a) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (M * Qm) * 1 := by
        gcongr
        refine c3_budget_le_one ι ?_ ?_ ?_
        · exact (mul_le_mul_of_nonneg_left (tsum_trAtoms_indicator_le n B μ) zero_le).trans
            (ofReal_rpow_mul_tsum_trBad_c3PaidLaw_le ι hmbad hPN
              (natCast_trGap_toNat_mul_log_two_le hξ hje hΔ heΔ))
        · exact (tsum_trAtoms_indicator_le n LB _).trans
            (tsum_trFreshLaw_trEStar_lt ι hξ hΔ heΔ (by exact_mod_cast hmsc) hje hPN hgap)
        · exact (tsum_trAtoms_c3PaidLaw_le n ξ e).trans
            (tsum_c3PaidPassage_lt_qMass hξ he hblack hω).le
    _ = _ := mul_one _

end CollatzPosDens
