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
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Dbad
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.Case3.C3BadJAbsorb
public import CollatzPosDens.Case3.C3GapRatio
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnHorTailSharp
public import CollatzPosDens.Renewal.RnListHorTail
public import CollatzPosDens.Renewal.RnListMarginal
public import CollatzPosDens.StoppingTrace.TrFreshMarginal

/-!
# The outer horizontal tail

Let `ι ∈ {o, b}` be a Fourier index, `e ∈ 𝒫`, `G ∈ ℕ`, and let `m ∈ ℕ` with `m ≥ D_bad(ι)`,
`P_*(ι) ≤ J = ⌊n/2⌋` and `G log 2 ≤ m log 9`. Then the fresh law gives the large-advance event a
small mass:
$$m^{A_*(ι)}\,\mu_{e,G}(\mathrm{Bad}^e_m(ι)) < \tfrac1{8000}.$$

Write `P_* = P_*(ι)` and an atom as `a = ((r, ℓ), β)`. Since
`j(y^e_{P_*}(a)) - j(e) = r + ∑_{k ≤ P_*} j(β^k)`, the event `Bad^e_m(ι)` lies in
`{r ≥ 158499 m / 200000} ∪ {∑_{k ≤ P_*} j(β^k) ≥ m / 200000}`. As
`log 9 / log 2 < 158497/50000`, `G ≤ 158497 m / 50000`, so on the first set
`r - G/4 ≥ m / 100000`, and the sharp horizontal tail of the first-passage law bounds its mass by
`6 e^{-m/2^{36}}`. The second set has mass at most `e^{P_*/2 - m/3200000}` by the
horizontal tail of hold lists. Both bounds pass through the displacement marginal of the fresh
law. The two rates are kept separate: `μ_{e,G}(Bad^e_m(ι)) ≤ 6 e^{-m/2^{36}} +
e^{P_*/2 - m/3200000}`, and the absorption lemma `c3_badJ_absorb` concludes.

## Main results

* `CollatzPosDens.c3_bad_mass_tsum_le`:
  `μ_{e,G}(Bad^e_m(ι)) ≤ 6 e^{-m/2^{36}} + e^{P_*(ι)/2 - m/3200000}`, as a sum in `[0, ∞]`,
  for `m ≥ 200000`, `P_*(ι) ≤ ⌊n/2⌋` and `G ≤ 158497 m / 50000`.
* `CollatzPosDens.c3_bad_mass_tsum_le_one`: `μ_{e,G}(Bad^e_m(ι)) ≤ 1`, as a sum in `[0, ∞]`.
* `CollatzPosDens.c3_bad_mass_summable`: the fresh law is summable on `Bad^e_m(ι)`.
* `CollatzPosDens.c3_bad_mass`: `m^{A_*(ι)} μ_{e,G}(Bad^e_m(ι)) < 1/8000`.

## Implementation notes

The mass `μ_{e,G}(Bad^e_m(ι))` is the unconditional real sum of `trFreshLaw` over the subtype
`trBad ι n e m`; `c3_bad_mass_summable` shows that it is a genuine sum. The power `m^{A_*}` is the
real power with exponent the cast of `A_*(ι) ∈ ℚ`. The hypothesis `e ∈ 𝒫` of the source plays no
role (the level `j(e)` cancels) and is dropped, which generalizes the source. The second event
is bounded with the real threshold `m / 20000` in the horizontal tail of hold lists, in place of
the integer threshold `10 ⌈m / 200000⌉`; the resulting bound is the same.

## References

* [Mazur, *Collatz positive density*], §10.6.
-/

@[expose] public section

namespace CollatzPosDens

open Real
open scoped ENNReal

/-- The advance `j(y^e_P(a)) - j(e)` of the fresh path at time `P ≤ |β|` is
`r + ∑_{k ≤ P} j(β^k)`. -/
private lemma c3BadMass_advance (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) {P : ℕ}
    (hP : P ≤ a.2.length) :
    bkJ (trFreshPath e a P) - bkJ e =
      (a.1.1 : ℤ) + ∑ i : Fin P, (chBlockPoint (a.2[(i : ℕ)]'(by omega))).1 := by
  have key : ∀ Q (hQ : Q ≤ a.2.length),
      chBlockPath a.2 Q = ∑ i : Fin Q, chBlockPoint (a.2[(i : ℕ)]'(by omega)) := by
    intro Q hQ
    induction Q with
    | zero => simp
    | succ Q ih =>
      rw [chBlockPath_succ _ (by omega), ih (by omega), Fin.sum_univ_castSucc]
      rfl
  rw [trFreshPath, trPath_eq_add_chBlockPath, key P hP]
  simp only [bkJ, Prod.fst_add, Prod.fst_sum]
  ring

/-- `G ≤ 158497 m / 50000` whenever `G log 2 ≤ m log 9`. -/
private lemma c3BadMass_le_of_log {G m : ℝ} (hm : 0 ≤ m) (hG : G * log 2 ≤ m * log 9) :
    G ≤ 158497 / 50000 * m := by
  have h2 : 0 < log 2 := log_pos (by norm_num)
  have h9 : log 9 < 158497 / 50000 * log 2 := (div_lt_iff₀ h2).1 log_nine_div_log_two_lt
  nlinarith

/-- The `F_G`-mass of the columns `200000 r ≥ 158499 m` is at most `6 e^{-m/2^{36}}`, for
`m ≥ 200000` and `G ≤ 158497 m / 50000`. -/
private lemma c3BadMass_tsum_fp_le {G m : ℕ} (hm : 200000 ≤ m)
    (hGm : (G : ℝ) ≤ 158497 / 50000 * m) :
    ∑' x : ℕ × ℤ, {x : ℕ × ℤ | 158499 * m ≤ 200000 * x.1}.indicator
      (fun x ↦ firstPassageLaw G ((x.1 : ℤ), x.2)) x ≤ 6 * exp (-m / 2 ^ 36) := by
  set t : ℝ := m / 100000 with ht
  have hm1 : (200000 : ℝ) ≤ m := by exact_mod_cast hm
  have ht2 : 2 ≤ t := by rw [ht, le_div_iff₀ (by norm_num)]; linarith
  set T : Set (ℤ × ℤ) := {y | t ≤ |(y.1 : ℝ) - G / 4|} with hT
  have hinj := natCast_prod_injective
  have hFT : Summable (T.indicator fun y ↦ firstPassageLaw G y) :=
    (hasSum_firstPassageLaw G).summable.indicator _
  have hFT0 : ∀ y, 0 ≤ T.indicator (fun y ↦ firstPassageLaw G y) y :=
    fun y ↦ Set.indicator_nonneg (fun _ _ ↦ firstPassageLaw_nonneg _ _) y
  -- the columns `200000 r ≥ 158499 m` lie in the tail `|r - G/4| ≥ t`
  have hle : ∀ x : ℕ × ℤ, {x : ℕ × ℤ | 158499 * m ≤ 200000 * x.1}.indicator
      (fun x ↦ firstPassageLaw G ((x.1 : ℤ), x.2)) x ≤
      T.indicator (fun y ↦ firstPassageLaw G y) ((x.1 : ℤ), x.2) := by
    intro x
    by_cases hx : 158499 * m ≤ 200000 * x.1
    · have hxT : ((x.1 : ℤ), x.2) ∈ T := by
        simp only [hT, Set.mem_ofPred_eq, Int.cast_natCast]
        have : (158499 * m : ℝ) ≤ 200000 * x.1 := by exact_mod_cast hx
        rw [abs_of_nonneg (by linarith)]
        linarith
      rw [Set.indicator_of_mem (by exact hx), Set.indicator_of_mem hxT]
    · rw [Set.indicator_of_notMem (by exact hx)]
      exact hFT0 _
  have h1 : ∑' x : ℕ × ℤ, {x : ℕ × ℤ | 158499 * m ≤ 200000 * x.1}.indicator
      (fun x ↦ firstPassageLaw G ((x.1 : ℤ), x.2)) x ≤
        ∑' y, T.indicator (fun y ↦ firstPassageLaw G y) y :=
    ((hFT.comp_injective hinj).of_nonneg_of_le
        (fun x ↦ Set.indicator_nonneg (fun _ _ ↦ firstPassageLaw_nonneg _ _) x) hle).tsum_le_tsum
      hle (hFT.comp_injective hinj) |>.trans (tsum_comp_le_tsum_of_inj hFT hFT0 hinj)
  have h2 : ∑' y, T.indicator (fun y ↦ firstPassageLaw G y) y =
      ∑' r : {r : ℤ // t ≤ |(r : ℝ) - G / 4|}, ∑' ℓ : ℤ, firstPassageLaw G ((r : ℤ), ℓ) := by
    rw [hFT.tsum_prod]
    refine Eq.trans ?_ (tsum_subtype {r : ℤ | t ≤ |(r : ℝ) - G / 4|}
      (fun r ↦ ∑' ℓ : ℤ, firstPassageLaw G (r, ℓ))).symm
    refine tsum_congr fun r ↦ ?_
    by_cases hr : t ≤ |(r : ℝ) - G / 4|
    · rw [Set.indicator_of_mem (by exact hr)]
      exact tsum_congr fun ℓ ↦ Set.indicator_of_mem (by exact hr) _
    · rw [Set.indicator_of_notMem (by exact hr)]
      exact (tsum_congr fun ℓ ↦ Set.indicator_of_notMem (by exact hr) _).trans tsum_zero
  -- the linear rate: `t / 256 = m / 25600000 ≥ m / 2^36`
  have hB : exp (-(t / 256)) ≤ exp (-m / 2 ^ 36) := by
    refine exp_le_exp.2 ?_
    rw [ht, neg_div, neg_le_neg_iff]
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  refine (h1.trans h2.le).trans ?_
  rcases le_or_gt G 5 with hG5 | hG6
  · refine (tsum_firstPassageLaw_hor_tail_le_of_le_five hG5 ht2).trans ?_
    have := exp_pos (-m / 2 ^ 36)
    linarith
  · refine (tsum_firstPassageLaw_hor_tail_le_of_six_le hG6 ht2).trans ?_
    -- the Gaussian rate: `t² / (2 (G - 4)) ≥ m / 2^36`, as `2 (G - 4) < 2 G ≤ 158497 m / 25000`
    have hG : (6 : ℝ) ≤ G := by exact_mod_cast hG6
    have hpos : (0 : ℝ) < 2 * ((G : ℝ) - 4) := by linarith
    have hA : exp (-(t ^ 2 / (2 * ((G : ℝ) - 4)))) ≤ exp (-m / 2 ^ 36) := by
      refine exp_le_exp.2 ?_
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) hpos, ht]
      have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
      nlinarith [mul_le_mul_of_nonneg_left hGm hm0]
    linarith

/-- The hold lists `h ∈ 𝒫^P` with `m ≤ 200000 ∑ᵢ j(hᵢ)` have mass at most
`e^{P/2 - m/3200000}`. -/
private lemma c3BadMass_tsum_hold_tail_le (P m : ℕ) :
    ∑' h : {h : Fin P → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
      ENNReal.ofReal (holdListLaw (fun i ↦ ((h.1 i).1.toNat, (h.1 i).2))) *
        (if (m : ℤ) ≤ 200000 * ∑ i, (h.1 i).1 then 1 else 0) ≤
      ENNReal.ofReal (exp (P / 2 - m / 3200000)) := by
  have hle := tsum_holdListLaw_bkPoints_mul_indicator_le
    (fun h : Fin P → ℤ × ℤ ↦ (m : ℤ) ≤ 200000 * ∑ i, (h i).1)
    (fun u ↦ (m : ℝ) / 20000 ≤ 10 * ∑ i, ((u i).1 : ℝ)) fun h hh hc ↦ by
      have hc' : (m : ℝ) ≤ 200000 * ∑ i, ((h i).1 : ℝ) := by exact_mod_cast hc
      have hs : ∑ i, (((h i).1.toNat : ℕ) : ℝ) = ∑ i, ((h i).1 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have := mem_bkPoints.1 (hh i)
        simp only [bkJ] at this
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      simp only [hs]
      linarith
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] at hle
  calc _ ≤ _ := hle
    _ ≤ ENNReal.ofReal (exp (P / 2 - m / 20000 / 160)) :=
        tsum_holdListLaw_horTail_le P ((m : ℝ) / 20000)
    _ = ENNReal.ofReal (exp (P / 2 - m / 3200000)) := by ring_nf

/-- The fresh mass of `Bad^e_m(ι)` is at most the displacement marginal of the event
`400 (r + ∑ᵢ j(hᵢ)) ≥ 317 m`. -/
private lemma c3BadMass_tsum_le_marginal (ι : FIndex) {n : ℕ} (e : ℤ × ℤ) (G m : ℕ)
    (hP : pStar ι ≤ n / 2) :
    ∑' a : trBad ι n e m, ENNReal.ofReal (trFreshLaw n e G a) ≤
      ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((rl.1 : ℤ), rl.2)) *
        ∑' h : {h : Fin (pStar ι) → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
          ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
            (if 317 * (m : ℤ) ≤ 400 * ((rl.1 : ℤ) + ∑ i, (h.1 i).1) then 1 else 0) := by
  set f : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e G a)
  set Gt : ℕ × ℤ → (Fin (pStar ι) → ℤ × ℤ) → ℝ≥0∞ := fun rl h ↦
    if 317 * (m : ℤ) ≤ 400 * ((rl.1 : ℤ) + ∑ i, (h i).1) then 1 else 0 with hGt
  -- Step 1: restrict to atoms, testing against the indicator of the event
  have h1 : ∑' a : trBad ι n e m, f a ≤ ∑' a : trAtoms n, f a * Gt a.1.1
      (fun i ↦ chBlockPoint (a.1.2[(i : ℕ)]'(by have := (mem_trAtoms.1 a.2).1; omega))) := by
    calc ∑' a : trBad ι n e m, f a
        = ∑' a : trBad ι n e m, (trBad ι n e m).indicator f
            (Set.inclusion (trBad_subset_trAtoms ι n e m) a : trAtoms n) :=
          tsum_congr fun a ↦ (Set.indicator_of_mem a.2 f).symm
      _ ≤ ∑' b : trAtoms n, (trBad ι n e m).indicator f b :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (Set.inclusion_injective (trBad_subset_trAtoms ι n e m))
            (fun b : trAtoms n ↦ (trBad ι n e m).indicator f b)
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun b ↦ ?_
          by_cases hb : (b : (ℕ × ℤ) × List (List ℤ × ℤ)) ∈ trBad ι n e m
          · rw [Set.indicator_of_mem hb]
            have hlen : pStar ι ≤ b.1.2.length := by
              have := (mem_trAtoms.1 b.2).1
              omega
            have hb2 := (mem_trBad.1 hb).2
            rw [c3BadMass_advance e b.1 hlen] at hb2
            have : Gt b.1.1 (fun i ↦ chBlockPoint (b.1.2[(i : ℕ)]'(by
                have := (mem_trAtoms.1 b.2).1; omega))) = 1 := by
              simp only [hGt, hb2, ↓reduceIte]
            rw [this, mul_one]
          · rw [Set.indicator_of_notMem hb]
            exact zero_le
  rwa [tsum_trFreshLaw_mul_chBlockPoint n e G (pStar ι) hP Gt] at h1

/-- Given the column `rl`, the hold lists completing the event `400 (r + ∑ᵢ j(hᵢ)) ≥ 317 m` have
mass at most `𝟙[200000 r ≥ 158499 m] + e^{P/2 - m/3200000}`. -/
private lemma c3BadMass_tsum_hold_mul_le (P m : ℕ) (rl : ℕ × ℤ) :
    ∑' h : {h : Fin P → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
          (if 317 * (m : ℤ) ≤ 400 * ((rl.1 : ℤ) + ∑ i, (h.1 i).1) then 1 else 0) ≤
      {x : ℕ × ℤ | 158499 * m ≤ 200000 * x.1}.indicator 1 rl +
        ENNReal.ofReal (exp (P / 2 - m / 3200000)) := by
  set c : ℝ≥0∞ := {x : ℕ × ℤ | 158499 * m ≤ 200000 * x.1}.indicator 1 rl
  calc _ ≤ ∑' h : {h : Fin P → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        (ENNReal.ofReal (holdListLaw (fun i ↦ ((h.1 i).1.toNat, (h.1 i).2))) * c +
          ENNReal.ofReal (holdListLaw (fun i ↦ ((h.1 i).1.toNat, (h.1 i).2))) *
            (if (m : ℤ) ≤ 200000 * ∑ i, (h.1 i).1 then 1 else 0)) := by
        refine ENNReal.tsum_le_tsum fun h ↦ ?_
        rw [← mul_add]
        refine mul_le_mul_right ?_ _
        split_ifs with hb hc
        · exact le_add_left le_rfl
        · by_cases h₁ : 158499 * m ≤ 200000 * rl.1
          · simp [c, h₁]
          · have : (158499 : ℤ) * m > 200000 * (rl.1 : ℤ) := by exact_mod_cast not_le.1 h₁
            omega
        · exact zero_le
        · exact zero_le
    _ = (∑' h : {h : Fin P → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
          ENNReal.ofReal (holdListLaw (fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)))) * c +
        ∑' h : {h : Fin P → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
          ENNReal.ofReal (holdListLaw (fun i ↦ ((h.1 i).1.toNat, (h.1 i).2))) *
            (if (m : ℤ) ≤ 200000 * ∑ i, (h.1 i).1 then 1 else 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * c + _ := add_le_add (mul_le_mul_left (tsum_ofReal_holdListLaw_bkPoints_le_one _) _)
        (c3BadMass_tsum_hold_tail_le _ _)
    _ = _ := by rw [one_mul]

/-- **Mass of the bad event.** For `m ≥ 200000`, `P_*(ι) ≤ ⌊n/2⌋` and `G ≤ 158497 m / 50000`,
`μ_{e,G}(Bad^e_m(ι)) ≤ 6 e^{-m/2^{36}} + e^{P_*(ι)/2 - m/3200000}`, as a sum in `[0, ∞]`. -/
theorem c3_bad_mass_tsum_le (ι : FIndex) {n : ℕ} (e : ℤ × ℤ) {G m : ℕ} (hm : 200000 ≤ m)
    (hP : pStar ι ≤ n / 2) (hGm : (G : ℝ) ≤ 158497 / 50000 * m) :
    ∑' a : trBad ι n e m, ENNReal.ofReal (trFreshLaw n e G a) ≤
      ENNReal.ofReal (6 * exp (-m / 2 ^ 36) + exp ((pStar ι : ℝ) / 2 - m / 3200000)) := by
  set F : ℕ × ℤ → ℝ := fun x ↦ firstPassageLaw G ((x.1 : ℤ), x.2)
  set A₁ : Set (ℕ × ℤ) := {x | 158499 * m ≤ 200000 * x.1}
  set E₂ : ℝ≥0∞ := ENNReal.ofReal (exp ((pStar ι : ℝ) / 2 - m / 3200000))
  have hF1 : ∑' x : ℕ × ℤ, ENNReal.ofReal (F x) * A₁.indicator 1 x =
      ENNReal.ofReal (∑' x : ℕ × ℤ, A₁.indicator F x) := by
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun x ↦ Set.indicator_nonneg (fun _ _ ↦ firstPassageLaw_nonneg _ _) x)
      ((summable_firstPassageLaw_natCast G).indicator _)]
    refine tsum_congr fun x ↦ ?_
    by_cases hx : x ∈ A₁
    · simp [F, Set.indicator_of_mem hx]
    · simp [F, Set.indicator_of_notMem hx]
  calc _ ≤ _ := c3BadMass_tsum_le_marginal ι e G m hP
    _ ≤ ∑' x : ℕ × ℤ, (ENNReal.ofReal (F x) * A₁.indicator 1 x + ENNReal.ofReal (F x) * E₂) :=
        ENNReal.tsum_le_tsum fun x ↦
          (mul_le_mul_right (c3BadMass_tsum_hold_mul_le (pStar ι) m x) _).trans
            (mul_add _ _ _).le
    _ = ENNReal.ofReal (∑' x : ℕ × ℤ, A₁.indicator F x) + (∑' x, ENNReal.ofReal (F x)) * E₂ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hF1]
    _ ≤ ENNReal.ofReal (6 * exp (-m / 2 ^ 36)) + 1 * E₂ :=
        add_le_add (ENNReal.ofReal_le_ofReal (c3BadMass_tsum_fp_le hm hGm))
          (mul_le_mul_left (tsum_ofReal_firstPassageLaw_natCast_le_one G) _)
    _ = ENNReal.ofReal (6 * exp (-m / 2 ^ 36) + exp ((pStar ι : ℝ) / 2 - m / 3200000)) := by
        rw [one_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The fresh mass of `Bad^e_m(ι)` is at most `1`, as a sum in `[0, ∞]`. -/
theorem c3_bad_mass_tsum_le_one (ι : FIndex) {n : ℕ} (e : ℤ × ℤ) (G m : ℕ)
    (hP : pStar ι ≤ n / 2) :
    ∑' a : trBad ι n e m, ENNReal.ofReal (trFreshLaw n e G a) ≤ 1 := by
  calc _ ≤ _ := c3BadMass_tsum_le_marginal ι e G m hP
    _ ≤ ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((rl.1 : ℤ), rl.2)) * 1 := by
        refine ENNReal.tsum_le_tsum fun rl ↦ mul_le_mul_right ?_ _
        refine (ENNReal.tsum_le_tsum fun h ↦ ?_).trans
          (tsum_ofReal_holdListLaw_bkPoints_le_one (pStar ι))
        split_ifs
        · rw [mul_one]
        · rw [mul_zero]
          exact zero_le
    _ ≤ 1 := by
        simp only [mul_one]
        exact tsum_ofReal_firstPassageLaw_natCast_le_one G

/-- The fresh law is summable on `Bad^e_m(ι)` whenever `P_*(ι) ≤ ⌊n/2⌋`; the hypotheses on `m`
and `G` of `c3_bad_mass_tsum_le` are not needed. -/
theorem c3_bad_mass_summable (ι : FIndex) {n : ℕ} (e : ℤ × ℤ) {G m : ℕ} (_hm : 1 ≤ m)
    (hP : pStar ι ≤ n / 2) (_hGm : (G : ℝ) ≤ 158497 / 50000 * m) :
    Summable fun a : trBad ι n e m ↦ trFreshLaw n e G a :=
  summable_trFreshLaw_of_tsum_ofReal_ne_top
    ((c3_bad_mass_tsum_le_one ι e G m hP).trans_lt ENNReal.one_lt_top).ne

/-- **Outer horizontal tail**. Let `ι` be a Fourier index, `G ∈ ℕ` and `m ∈ ℕ` with
`m ≥ D_bad(ι)`, `P_*(ι) ≤ ⌊n/2⌋` and `G log 2 ≤ m log 9`. Then
`m^{A_*(ι)} μ_{e,G}(Bad^e_m(ι)) < 1/8000`. -/
@[collatz_pos_dens "lem_c3_bad_mass"]
theorem c3_bad_mass (ι : FIndex) {n : ℕ} (e : ℤ × ℤ) {G m : ℕ} (hm : (Dbad ι : ℝ) ≤ m)
    (hP : pStar ι ≤ n / 2) (hG : (G : ℝ) * log 2 ≤ m * log 9) :
    (m : ℝ) ^ (Aexp ι : ℝ) * ∑' a : trBad ι n e m, trFreshLaw n e G a < 1 / 8000 := by
  have hm2 : 200000 ≤ m := by
    have h' : (2 : ℝ) ^ 43 ≤ (Dbad ι : ℝ) := by exact_mod_cast two_pow_43_le_Dbad ι
    exact_mod_cast (show (200000 : ℝ) ≤ m by linarith)
  have hGm := c3BadMass_le_of_log (Nat.cast_nonneg m) hG
  have hB := c3_bad_mass_tsum_le ι e hm2 hP hGm
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _)
    (c3_bad_mass_summable ι e (by omega) hP hGm)] at hB
  have hB' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hB
  calc (m : ℝ) ^ (Aexp ι : ℝ) * ∑' a : trBad ι n e m, trFreshLaw n e G a
      ≤ (m : ℝ) ^ (Aexp ι : ℝ) *
          (6 * exp (-m / 2 ^ 36) + exp ((pStar ι : ℝ) / 2 - m / 3200000)) := by
        gcongr
    _ < 1 / 8000 := c3_badJ_absorb ι hm

end CollatzPosDens
