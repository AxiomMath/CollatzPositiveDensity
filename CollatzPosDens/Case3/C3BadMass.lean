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
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.Dbad
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.Case3.C3BadJAbsorb
public import CollatzPosDens.Case3.C3GapRatio
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnHorTail
public import CollatzPosDens.Renewal.RnListHorTail
public import CollatzPosDens.Renewal.RnListMarginal
public import CollatzPosDens.StoppingTrace.TrFreshMarginal

/-!
# The outer horizontal tail

Let `e ∈ ℤ × ℤ`, `G ∈ ℕ`, and let `m ∈ ℕ` with `m ≥ D_bad`, `P_* ≤ J = ⌊n/2⌋` and
`G log 2 ≤ m log 9`. Then the fresh law gives the large-advance event a small mass:
$$m^{A_*}\,\mu_{e,G}(\mathrm{Bad}^e_m) < \tfrac1{8000}.$$

Write an atom as `a = ((r, ℓ), β)`. Since `j(y^e_{P_*}(a)) - j(e) = r + ∑_{k ≤ P_*} j(β^k)`, the
event `Bad^e_m` lies in `{r ≥ 158499 m / 200000} ∪ {∑_{k ≤ P_*} j(β^k) ≥ m / 200000}`. As
`log 9 / log 2 < 158497/50000`, `G ≤ 158497 m / 50000`, so on the first set
`r - G/4 ≥ m / 100000`, and the horizontal tail of the first-passage law bounds its mass by
`2^{55} e^{-m/2^{51}}`. The second set has mass at most `e^{P_*/2 - m/3200000}` by the
horizontal tail of hold lists. Both bounds pass through the displacement marginal of the fresh
law. Hence `μ_{e,G}(Bad^e_m) ≤ (2^{55} + e^{P_*/2}) e^{-m/2^{51}}`, and the absorption lemma
`c3_badJ_absorb` concludes.

## Main results

* `CollatzPosDens.c3_bad_mass_tsum_le`: `μ_{e,G}(Bad^e_m) ≤ (2^{55} + e^{P_*/2}) e^{-m/2^{51}}`,
  as a sum in `[0, ∞]`, for `m ≥ 1`, `P_* ≤ ⌊n/2⌋` and `G ≤ 158497 m / 50000`.
* `CollatzPosDens.c3_bad_mass_summable`: the fresh law is summable on `Bad^e_m`.
* `CollatzPosDens.c3_bad_mass`: `m^{A_*} μ_{e,G}(Bad^e_m) < 1/8000`.

## Implementation notes

The mass `μ_{e,G}(Bad^e_m)` is the unconditional real sum of `trFreshLaw` over the subtype
`trBad n e m`; `c3_bad_mass_summable` shows that it is a genuine sum. The power `m^{A_*}` is the
real power with exponent the cast of `A_* ∈ ℚ`. The base point `e` is arbitrary: the level `j(e)`
cancels, so no hypothesis `e ∈ 𝒫` is needed, unlike in [mazur2026]. The second event
is bounded with the real threshold `m / 20000` in the horizontal tail of hold lists, in place of
the integer threshold `10 ⌈m / 200000⌉`; the resulting bound is the same.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
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
  have h9 : log 9 < 158497 / 50000 * log 2 := by
    have := log_nine_div_log_two_lt
    rwa [div_lt_iff₀ h2] at this
  nlinarith

/-- The `F_G`-mass of the columns `200000 r ≥ 158499 m` is at most `2^{55} e^{-m/2^{51}}`. -/
private lemma c3BadMass_tsum_fp_le {G m : ℕ} (hm : 1 ≤ m) (hGm : (G : ℝ) ≤ 158497 / 50000 * m) :
    ∑' x : ℕ × ℤ, {x : ℕ × ℤ | 158499 * m ≤ 200000 * x.1}.indicator
      (fun x ↦ firstPassageLaw G ((x.1 : ℤ), x.2)) x ≤ 2 ^ 55 * exp (-m / 2 ^ 51) := by
  set t : ℝ := m / 100000 with ht
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set T : Set (ℤ × ℤ) := {y | t ≤ |(y.1 : ℝ) - G / 4|} with hT
  have hinj := natCast_prod_injective
  have hF := (hasSum_firstPassageLaw G).summable
  have hFT : Summable (T.indicator fun y ↦ firstPassageLaw G y) := hF.indicator _
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
  have h3 := tsum_firstPassageLaw_hor_tail_le G t
  -- both exponents are at least `m / 2^51`
  have hg1 : 1 + (G : ℝ) ≤ 21 / 5 * m := by linarith
  have hA : -(t ^ 2 / (2 ^ 15 * (1 + G))) ≤ -m / 2 ^ 51 := by
    have hpos : (0 : ℝ) < 2 ^ 15 * (1 + G) := by positivity
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) hpos, ht]
    nlinarith
  have hB : -(t / 256) ≤ -m / 2 ^ 51 := by
    rw [ht, neg_div, neg_le_neg_iff]
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ ≤ 2 ^ 54 * (exp (-m / 2 ^ 51) + exp (-m / 2 ^ 51)) := by
        gcongr
    _ = 2 ^ 55 * exp (-m / 2 ^ 51) := by ring

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

/-- The fresh mass of `Bad^e_m` is at most the displacement marginal of the event
`400 (r + ∑ᵢ j(hᵢ)) ≥ 317 m`. -/
private lemma c3BadMass_tsum_le_marginal {n : ℕ} (e : ℤ × ℤ) (G m : ℕ) (hP : pStar ≤ n / 2) :
    ∑' a : trBad n e m, ENNReal.ofReal (trFreshLaw n e G a) ≤
      ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw G ((rl.1 : ℤ), rl.2)) *
        ∑' h : {h : Fin pStar → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
          ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
            (if 317 * (m : ℤ) ≤ 400 * ((rl.1 : ℤ) + ∑ i, (h.1 i).1) then 1 else 0) := by
  set f : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e G a)
  set Gt : ℕ × ℤ → (Fin pStar → ℤ × ℤ) → ℝ≥0∞ := fun rl h ↦
    if 317 * (m : ℤ) ≤ 400 * ((rl.1 : ℤ) + ∑ i, (h i).1) then 1 else 0 with hGt
  -- Step 1: restrict to atoms, testing against the indicator of the event
  have h1 : ∑' a : trBad n e m, f a ≤ ∑' a : trAtoms n, f a * Gt a.1.1
      (fun i ↦ chBlockPoint (a.1.2[(i : ℕ)]'(by have := (mem_trAtoms.1 a.2).1; omega))) := by
    calc ∑' a : trBad n e m, f a
        = ∑' a : trBad n e m, (trBad n e m).indicator f
            (Set.inclusion (trBad_subset_trAtoms n e m) a : trAtoms n) :=
          tsum_congr fun a ↦ (Set.indicator_of_mem a.2 f).symm
      _ ≤ ∑' b : trAtoms n, (trBad n e m).indicator f b :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (Set.inclusion_injective (trBad_subset_trAtoms n e m))
            (fun b : trAtoms n ↦ (trBad n e m).indicator f b)
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun b ↦ ?_
          by_cases hb : (b : (ℕ × ℤ) × List (List ℤ × ℤ)) ∈ trBad n e m
          · rw [Set.indicator_of_mem hb]
            have hlen : pStar ≤ b.1.2.length := by
              have := (mem_trAtoms.1 b.2).1
              omega
            have hadv := c3BadMass_advance e b.1 hlen
            have hb2 := (mem_trBad.1 hb).2
            rw [hadv] at hb2
            have : Gt b.1.1 (fun i ↦ chBlockPoint (b.1.2[(i : ℕ)]'(by
                have := (mem_trAtoms.1 b.2).1; omega))) = 1 := by
              simp only [hGt, hb2, ↓reduceIte]
            rw [this, mul_one]
          · rw [Set.indicator_of_notMem hb]
            exact zero_le
  rwa [tsum_trFreshLaw_mul_chBlockPoint n e G pStar hP Gt] at h1

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

/-- **Mass of the bad event.** For `m ≥ 1`, `P_* ≤ ⌊n/2⌋` and `G ≤ 158497 m / 50000`,
`μ_{e,G}(Bad^e_m) ≤ (2^{55} + e^{P_*/2}) e^{-m/2^{51}}`, as a sum in `[0, ∞]`. -/
theorem c3_bad_mass_tsum_le {n : ℕ} (e : ℤ × ℤ) {G m : ℕ} (hm : 1 ≤ m) (hP : pStar ≤ n / 2)
    (hGm : (G : ℝ) ≤ 158497 / 50000 * m) :
    ∑' a : trBad n e m, ENNReal.ofReal (trFreshLaw n e G a) ≤
      ENNReal.ofReal ((2 ^ 55 + exp ((pStar : ℝ) / 2)) * exp (-m / 2 ^ 51)) := by
  set F : ℕ × ℤ → ℝ := fun x ↦ firstPassageLaw G ((x.1 : ℤ), x.2)
  set A₁ : Set (ℕ × ℤ) := {x | 158499 * m ≤ 200000 * x.1}
  set E₂ : ℝ≥0∞ := ENNReal.ofReal (exp ((pStar : ℝ) / 2 - m / 3200000))
  have hF1 : ∑' x : ℕ × ℤ, ENNReal.ofReal (F x) * A₁.indicator 1 x =
      ENNReal.ofReal (∑' x : ℕ × ℤ, A₁.indicator F x) := by
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun x ↦ Set.indicator_nonneg (fun _ _ ↦ firstPassageLaw_nonneg _ _) x)
      ((summable_firstPassageLaw_natCast G).indicator _)]
    refine tsum_congr fun x ↦ ?_
    by_cases hx : x ∈ A₁
    · simp [F, Set.indicator_of_mem hx]
    · simp [F, Set.indicator_of_notMem hx]
  have hexp : exp ((pStar : ℝ) / 2 - m / 3200000) ≤ exp ((pStar : ℝ) / 2) * exp (-m / 2 ^ 51) := by
    rw [← exp_add, exp_le_exp]
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  calc _ ≤ _ := c3BadMass_tsum_le_marginal e G m hP
    _ ≤ ∑' x : ℕ × ℤ, (ENNReal.ofReal (F x) * A₁.indicator 1 x + ENNReal.ofReal (F x) * E₂) :=
        ENNReal.tsum_le_tsum fun x ↦
          (mul_le_mul_right (c3BadMass_tsum_hold_mul_le pStar m x) _).trans (mul_add _ _ _).le
    _ = ENNReal.ofReal (∑' x : ℕ × ℤ, A₁.indicator F x) + (∑' x, ENNReal.ofReal (F x)) * E₂ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hF1]
    _ ≤ ENNReal.ofReal (2 ^ 55 * exp (-m / 2 ^ 51)) + 1 * E₂ :=
        add_le_add (ENNReal.ofReal_le_ofReal (c3BadMass_tsum_fp_le hm hGm))
          (mul_le_mul_left (tsum_ofReal_firstPassageLaw_natCast_le_one G) _)
    _ ≤ ENNReal.ofReal (2 ^ 55 * exp (-m / 2 ^ 51)) +
          ENNReal.ofReal (exp ((pStar : ℝ) / 2) * exp (-m / 2 ^ 51)) := by
        rw [one_mul]
        exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hexp)
    _ = ENNReal.ofReal ((2 ^ 55 + exp ((pStar : ℝ) / 2)) * exp (-m / 2 ^ 51)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The fresh law is summable on `Bad^e_m`, under the hypotheses of `c3_bad_mass_tsum_le`. -/
theorem c3_bad_mass_summable {n : ℕ} (e : ℤ × ℤ) {G m : ℕ} (hm : 1 ≤ m) (hP : pStar ≤ n / 2)
    (hGm : (G : ℝ) ≤ 158497 / 50000 * m) :
    Summable fun a : trBad n e m ↦ trFreshLaw n e G a := by
  have h := (c3_bad_mass_tsum_le e hm hP hGm).trans_lt ENNReal.ofReal_lt_top
  exact summable_trFreshLaw_of_tsum_ofReal_ne_top h.ne

/-- **Outer horizontal tail**. Let `G ∈ ℕ` and `m ∈ ℕ` with `m ≥ D_bad`, `P_* ≤ ⌊n/2⌋` and
`G log 2 ≤ m log 9`. Then `m^{A_*} μ_{e,G}(Bad^e_m) < 1/8000`. -/
@[collatz_pos_dens "lem_c3_bad_mass"]
theorem c3_bad_mass {n : ℕ} (e : ℤ × ℤ) {G m : ℕ} (hm : (Dbad : ℝ) ≤ m) (hP : pStar ≤ n / 2)
    (hG : (G : ℝ) * log 2 ≤ m * log 9) :
    (m : ℝ) ^ (Aexp : ℝ) * ∑' a : trBad n e m, trFreshLaw n e G a < 1 / 8000 := by
  have hm1 : 1 ≤ m := by
    have h := two_pow_mul_pStar_add_le_Dbad
    have h' : (2 ^ 53 * ((pStar : ℝ) + 65)) ≤ (Dbad : ℝ) := by exact_mod_cast h
    have : (1 : ℝ) ≤ m := by
      have : (0 : ℝ) ≤ pStar := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  have hGm := c3BadMass_le_of_log (Nat.cast_nonneg m) hG
  have hB := c3_bad_mass_tsum_le e hm1 hP hGm
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _)
    (c3_bad_mass_summable e hm1 hP hGm)] at hB
  have hB' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hB
  calc (m : ℝ) ^ (Aexp : ℝ) * ∑' a : trBad n e m, trFreshLaw n e G a
      ≤ (m : ℝ) ^ (Aexp : ℝ) * ((2 ^ 55 + exp ((pStar : ℝ) / 2)) * exp (-m / 2 ^ 51)) := by
        gcongr
    _ = (m : ℝ) ^ (Aexp : ℝ) * (2 ^ 55 + exp ((pStar : ℝ) / 2)) * exp (-m / 2 ^ 51) := by
        ring
    _ < 1 / 8000 := c3_badJ_absorb hm

end CollatzPosDens
