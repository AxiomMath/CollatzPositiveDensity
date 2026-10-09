/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnListMarginal
public import CollatzPosDens.Renewal.RnListVerLow
public import CollatzPosDens.StoppingTrace.TrClear
public import CollatzPosDens.StoppingTrace.TrClearNumeric
public import CollatzPosDens.StoppingTrace.TrFreshMarginal
public import CollatzPosDens.Transfer.Beta
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Failed clearing is rare

Let `J = ⌊n/2⌋` and suppose `pStar ≤ J`. Under the fresh law `μ_{e,g} = trFreshLaw n e g`, the
failed clearing event `Clr = trClear n` has mass `μ_{e,g}(Clr) < 2^{-43}`.

Write `v = 4095/4096`. For a window `{q + 1, …, q + h}` with `q + h ≤ J` and a threshold `Y`,
the atoms whose blocks gain at most `Y` over the window have mass at most `v^{(127/10) h - Y}`:
by the displacement marginal of the fresh law and `∑ F_g ≤ 1`, the mass is at most the
`η^{⊗(q+h)}`-mass of the hold lists whose last `h` entries have total height at most `Y`; the
first `q` entries contribute a factor `1`, and the lower vertical tail of `η^{⊗h}` gives the
bound. With `h_* = windowLength`, `β_* = betaStar` and `K_* = Kstar`, for `h = h_*(q)` and
`Y = (13/9) β_*(q)`, since `35 h_*(q) ≥ 4 β_*(q)`, `K_* (q + 1) ≤ β_*(q)` and
`11 K_* ≥ 32 · 1575 · 4096`, the exponent is at least `(11/1575) β_*(q) ≥ 32 · 4096 (q + 1)`, and
as `log v ≤ -1/4096` the window `q` contributes at most `e^{-32 (q + 1)}`. Summing over `q`,
`μ_{e,g}(Clr) ≤ e^{-32}/(1 - e^{-32}) ≤ 2 e^{-32}`, which is less than `2^{-43}` because
`44 log 2 < 32`.

## Main results

* `CollatzPosDens.tsum_trFreshLaw_trClearWindow_le`: the mass of a single failed window.
* `CollatzPosDens.tsum_trFreshLaw_trClear_lt`: `μ_{e,g}(Clr) < 2^{-43}`, as a sum in
  `[0, ∞]`.
* `CollatzPosDens.summable_trFreshLaw_trClear`: the fresh law is summable on `Clr`.
* `CollatzPosDens.tsum_trFreshLaw_trClear_lt_real`: `μ_{e,g}(Clr) < 2^{-43}`, as a real sum.

## Implementation notes

The mass `μ_{e,g}(Clr)` is the unconditional sum over the subtype `Clr` of
`ENNReal.ofReal (trFreshLaw n e g a)`, as in the displacement marginal of the fresh law; this
form needs no summability assumption, and the real form follows. The hypotheses `n ≥ 1`, that
`ξ ∈ G_n` is a unit and that `e ∈ 𝒫` play no role in the bound and are dropped; only
`pStar ≤ ⌊n/2⌋` is used, to place every admissible window inside the block list.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal
open Real

/-- The window gain as a sum over `range h`. -/
private lemma trClearMass_gain_eq_sum_range (β : List (List ℤ × ℤ)) (q h : ℕ) :
    trClearGain β q h =
      ∑ k ∈ Finset.range h, ((β[q + k]?).map fun b => (chBlockPoint b).2).getD 0 := by
  induction h with
  | zero => simp
  | succ h ih => rw [trClearGain_succ, ih, Finset.sum_range_succ]

/-- Inside the list, the window gain is `∑_{i < h} l(bpt(β[q + i]))`. -/
private lemma trClearMass_gain_eq_sum_fin (β : List (List ℤ × ℤ)) (q h : ℕ)
    (hle : q + h ≤ β.length) :
    (trClearGain β q h : ℝ) =
      ∑ i : Fin h, ((chBlockPoint (β[q + (i : ℕ)]'(by omega))).2 : ℝ) := by
  rw [trClearMass_gain_eq_sum_range, ← Fin.sum_univ_eq_sum_range, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.getElem?_eq_getElem (by omega)]
  simp

/-- The hold lists of length `q + h` whose last `h` entries have total height at most `Y` have
`η^{⊗(q+h)}`-mass at most `v^{(127/10) h - Y}`, `v = 4095/4096`. -/
private lemma trClearMass_hold_window (q h : ℕ) (Y : ℝ) :
    ∑' u : {u : Fin (q + h) → ℕ × ℤ //
        (∀ i, 1 ≤ (u i).1) ∧ ∑ i : Fin h, ((u (Fin.natAdd q i)).2 : ℝ) ≤ Y},
      ENNReal.ofReal (holdListLaw u.1) ≤
        ENNReal.ofReal ((4095 / 4096 : ℝ) ^ (127 / 10 * (h : ℝ) - Y)) := by
  set A : Set (Fin q → ℕ × ℤ) := {x | ∀ i, 1 ≤ (x i).1} with hA
  set B : Set (Fin h → ℕ × ℤ) := {y | (∀ i, 1 ≤ (y i).1) ∧ ∑ i, ((y i).2 : ℝ) ≤ Y} with hB
  set S : Set (Fin (q + h) → ℕ × ℤ) :=
    {u | (∀ i, 1 ≤ (u i).1) ∧ ∑ i : Fin h, ((u (Fin.natAdd q i)).2 : ℝ) ≤ Y} with hS
  have hsplit : ∀ x y, S.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) (Fin.append x y) =
      A.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) x *
        B.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) y := by
    intro x y
    have hmem : Fin.append x y ∈ S ↔ x ∈ A ∧ y ∈ B := by
      simp only [hS, hA, hB, Set.mem_ofPred_eq, Fin.forall_fin_add, Fin.append_left,
        Fin.append_right]
      tauto
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem (hmem.2 ⟨hx, hy⟩), Set.indicator_of_mem hx,
        Set.indicator_of_mem hy, holdListLaw_append, ENNReal.ofReal_mul (holdListLaw_nonneg _)]
    · rw [Set.indicator_of_notMem (fun h ↦ hy (hmem.1 h).2), Set.indicator_of_notMem hy,
        mul_zero]
    · rw [Set.indicator_of_notMem (fun h ↦ hx (hmem.1 h).1), Set.indicator_of_notMem hx,
        zero_mul]
    · rw [Set.indicator_of_notMem (fun h ↦ hx (hmem.1 h).1), Set.indicator_of_notMem hx,
        zero_mul]
  have hAm : ∑' x, A.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) x = 1 := by
    rw [← tsum_subtype A (fun u ↦ ENNReal.ofReal (holdListLaw u))]
    exact tsum_ofReal_holdListLaw q
  have hBm : ∑' y, B.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) y ≤
      ENNReal.ofReal ((4095 / 4096 : ℝ) ^ (127 / 10 * (h : ℝ) - Y)) := by
    rw [← tsum_subtype B (fun u ↦ ENNReal.ofReal (holdListLaw u))]
    exact tsum_holdListLaw_verLow_le h Y
  calc ∑' u : S, ENNReal.ofReal (holdListLaw u.1)
      = ∑' p : (Fin q → ℕ × ℤ) × (Fin h → ℕ × ℤ),
          S.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) (Fin.append p.1 p.2) := by
        rw [tsum_subtype S (fun u ↦ ENNReal.ofReal (holdListLaw u)),
          ← (Fin.appendEquiv q h).tsum_eq]
        rfl
    _ = (∑' x, A.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) x) *
          ∑' y, B.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) y := by
        simp_rw [hsplit]
        rw [ENNReal.tsum_prod (f := fun x y ↦
          A.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) x *
            B.indicator (fun u ↦ ENNReal.ofReal (holdListLaw u)) y), ← ENNReal.tsum_mul_right]
        exact tsum_congr fun x ↦ ENNReal.tsum_mul_left
    _ ≤ _ := by rwa [hAm, one_mul]

/-- **Mass of a failed window.** If `q + h ≤ ⌊n/2⌋`, the fresh atoms whose blocks gain at most
`Y` over the window `{q + 1, …, q + h}` have `μ_{e,g}`-mass at most `v^{(127/10) h - Y}`, where
`v = 4095/4096`. -/
theorem tsum_trFreshLaw_trClearWindow_le (n : ℕ) (e : ℤ × ℤ) (g q h : ℕ) (Y : ℝ)
    (hq : q + h ≤ n / 2) :
    ∑' a : {a | a ∈ trAtoms n ∧ (trClearGain a.2 q h : ℝ) ≤ Y},
        ENNReal.ofReal (trFreshLaw n e g a) ≤
      ENNReal.ofReal ((4095 / 4096 : ℝ) ^ (127 / 10 * (h : ℝ) - Y)) := by
  set C : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
    {a | a ∈ trAtoms n ∧ (trClearGain a.2 q h : ℝ) ≤ Y}
  set ψ : (Fin (q + h) → ℤ × ℤ) → Prop :=
    fun h' ↦ ∑ i : Fin h, ((h' (Fin.natAdd q i)).2 : ℝ) ≤ Y with hψ
  set G : ℕ × ℤ → (Fin (q + h) → ℤ × ℤ) → ℝ≥0∞ := fun _ h' ↦ {h' | ψ h'}.indicator 1 h'
    with hG
  set φ : trAtoms n → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e g a) *
    G a.1.1 (fun i ↦ chBlockPoint (a.1.2[(i : ℕ)]'(by
      have := (mem_trAtoms.1 a.2).1; omega))) with hφ
  have hsub : C ⊆ trAtoms n := fun _ ha ↦ ha.1
  set B := ENNReal.ofReal ((4095 / 4096 : ℝ) ^ (127 / 10 * (h : ℝ) - Y))
  have hinner : ∀ rl : ℕ × ℤ, ∑' h' : {h' : Fin (q + h) → ℤ × ℤ // ∀ i, h' i ∈ bkPoints},
      ENNReal.ofReal (holdListLaw fun i ↦ ((h'.1 i).1.toNat, (h'.1 i).2)) * G rl h'.1 ≤ B :=
    fun rl ↦ (tsum_holdListLaw_bkPoints_mul_indicator_le ψ
      (fun u ↦ ∑ i : Fin h, ((u (Fin.natAdd q i)).2 : ℝ) ≤ Y) (fun _ _ hh ↦ hh)).trans
      (trClearMass_hold_window q h Y)
  calc ∑' a : C, ENNReal.ofReal (trFreshLaw n e g a)
      ≤ ∑' a : C, φ (Set.inclusion hsub a) := by
        refine ENNReal.tsum_le_tsum fun a ↦ le_of_eq ?_
        have hlen : q + h ≤ a.1.2.length := by rwa [(mem_trAtoms.1 a.2.1).1]
        have hmem : ψ (fun i ↦ chBlockPoint (a.1.2[(i : ℕ)]'(by
            have := (mem_trAtoms.1 a.2.1).1; omega))) := by
          have h2 := a.2.2
          rw [trClearMass_gain_eq_sum_fin _ _ _ hlen] at h2
          simpa [hψ] using h2
        simp only [hφ, hG, Set.inclusion]
        rw [Set.indicator_of_mem (show _ ∈ {h' | ψ h'} from hmem), Pi.one_apply, mul_one]
    _ ≤ ∑' a : trAtoms n, φ a :=
        ENNReal.tsum_comp_le_tsum_of_injective (Set.inclusion_injective hsub) φ
    _ = ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) *
        ∑' h' : {h' : Fin (q + h) → ℤ × ℤ // ∀ i, h' i ∈ bkPoints},
          ENNReal.ofReal (holdListLaw fun i ↦ ((h'.1 i).1.toNat, (h'.1 i).2)) * G rl h'.1 :=
        tsum_trFreshLaw_mul_chBlockPoint n e g (q + h) hq G
    _ ≤ ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) * B :=
        ENNReal.tsum_le_tsum fun rl ↦ by
          gcongr
          exact hinner rl
    _ ≤ B := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' (tsum_ofReal_firstPassageLaw_natCast_le_one g)

/-- The exponent bound: `v^{(127/10) h_*(q) - (13/9) β_*(q)} ≤ (e^{-32})^{q+1}`. -/
private lemma trClearMass_rpow_le (q : ℕ) :
    (4095 / 4096 : ℝ) ^ (127 / 10 * (windowLength q : ℝ) - 13 / 9 * (betaStar q : ℝ)) ≤
      exp (-32) ^ (q + 1) := by
  set x : ℝ := 127 / 10 * (windowLength q : ℝ) - 13 / 9 * (betaStar q : ℝ) with hx
  have hw : (4 * (betaStar q : ℝ) + 35 * 8192) ≤ 35 * (windowLength q : ℝ) := by
    exact_mod_cast windowLength_mul_ge q
  have hK : (Kstar : ℝ) * ((q : ℝ) + 1) ≤ (betaStar q : ℝ) := by
    exact_mod_cast Kstar_mul_le_betaStar q
  have hnum := Kstar_clear_numeric_cast (R := ℝ)
  have hq1 : (0 : ℝ) ≤ (q : ℝ) + 1 := by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have hKq : (32 * 1575 * 4096 : ℝ) * ((q : ℝ) + 1) ≤ 11 * ((Kstar : ℝ) * ((q : ℝ) + 1)) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hnum hq1
  have hxlow : 32 * 4096 * ((q : ℝ) + 1) ≤ x := by
    rw [hx]
    nlinarith
  have hv0 : (0 : ℝ) < 4095 / 4096 := by norm_num
  have hlog : Real.log (4095 / 4096 : ℝ) ≤ -(1 / 4096) := by
    linarith [Real.log_le_sub_one_of_pos hv0]
  rw [Real.rpow_def_of_pos hv0, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  push_cast
  have hx0 : 0 ≤ x := by nlinarith
  nlinarith

/-- `e^{-32} / (1 - e^{-32}) < 2^{-43}`. -/
private lemma trClearMass_geom_lt :
    exp (-32) * (1 - exp (-32))⁻¹ < (2 : ℝ) ^ (-43 : ℤ) := by
  set r := exp (-32) with hr
  have hr0 : 0 < r := exp_pos _
  -- `2^44 < e^32`, since `44 log 2 < 32`.
  have h44 : (2 : ℝ) ^ 44 < exp 32 := by
    have h2 : (2 : ℝ) ^ 44 = exp (44 * Real.log 2) := by
      rw [show ((44 : ℝ)) = ((44 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log two_pos]
    rw [h2]
    apply Real.exp_lt_exp.2
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hr44 : r * 2 ^ 44 < 1 := by
    rw [← show r * exp 32 = 1 by rw [hr, ← Real.exp_add]; norm_num]
    gcongr
  have hrhalf : r ≤ 1 / 2 := by nlinarith
  have h1r : 0 < 1 - r := by linarith
  rw [zpow_neg, ← div_eq_mul_inv, div_lt_iff₀ h1r]
  have key : r * 2 ^ 43 < 1 - r := by linarith [show r * 2 ^ 44 = 2 * (r * 2 ^ 43) by ring]
  rwa [show (2 : ℝ) ^ (43 : ℤ) = 2 ^ 43 by norm_num, inv_mul_eq_div, lt_div_iff₀ (by positivity)]

/-- **Failed clearing is rare.** If `P_* ≤ ⌊n/2⌋`, the failed clearing event has fresh-law mass
`∑_{a ∈ Clr} μ_{e,g}(a) < 2^{-43}`, as a sum in `[0, ∞]`. -/
@[collatz_pos_dens "lem_tr_clear_mass"]
theorem tsum_trFreshLaw_trClear_lt (n : ℕ) (e : ℤ × ℤ) (g : ℕ) (hP : pStar ≤ n / 2) :
    ∑' a : trClear n, ENNReal.ofReal (trFreshLaw n e g a) <
      ENNReal.ofReal ((2 : ℝ) ^ (-43 : ℤ)) := by
  set f : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e g a)
  set Cq : ℕ → Set ((ℕ × ℤ) × List (List ℤ × ℤ)) := fun q ↦
    {a | a ∈ trAtoms n ∧ q + windowLength q ≤ pStar - 1 ∧
      (trClearGain a.2 q (windowLength q) : ℝ) ≤ 13 / 9 * (betaStar q : ℝ)} with hCq
  have hU : trClear n = ⋃ q, Cq q := by
    ext a
    simp only [mem_trClear, Set.mem_iUnion, hCq, Set.mem_ofPred_eq]
    exact ⟨fun ⟨ha, q, h1, h2⟩ ↦ ⟨q, ha, h1, h2⟩, fun ⟨q, ha, h1, h2⟩ ↦ ⟨ha, q, h1, h2⟩⟩
  set r : ℝ := exp (-32)
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hsum : Summable fun q : ℕ ↦ r ^ (q + 1) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one hr0 hr1).mul_right r
  have hq : ∀ q, ∑' a : Cq q, f a ≤ ENNReal.ofReal (r ^ (q + 1)) := by
    intro q
    by_cases hqP : q + windowLength q ≤ pStar - 1
    · have hsub : Cq q ⊆ {a | a ∈ trAtoms n ∧
          (trClearGain a.2 q (windowLength q) : ℝ) ≤ 13 / 9 * (betaStar q : ℝ)} :=
        fun a ha ↦ ⟨ha.1, ha.2.2⟩
      refine (ENNReal.tsum_mono_subtype f hsub).trans ?_
      refine (tsum_trFreshLaw_trClearWindow_le n e g q (windowLength q) _ (by omega)).trans ?_
      exact ENNReal.ofReal_le_ofReal (trClearMass_rpow_le q)
    · rw [ENNReal.tsum_eq_zero.2 fun a ↦ absurd a.2.2.1 hqP]
      exact zero_le
  rw [hU]
  calc ∑' a : ⋃ q, Cq q, f a ≤ ∑' q, ∑' a : Cq q, f a := ENNReal.tsum_iUnion_le_tsum f Cq
    _ ≤ ∑' q : ℕ, ENNReal.ofReal (r ^ (q + 1)) := ENNReal.tsum_le_tsum hq
    _ = ENNReal.ofReal (∑' q : ℕ, r ^ (q + 1)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ pow_nonneg hr0 _) hsum).symm
    _ < ENNReal.ofReal ((2 : ℝ) ^ (-43 : ℤ)) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        simp_rw [pow_succ']
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        exact trClearMass_geom_lt

/-- The fresh law is summable on the failed clearing event, when `P_* ≤ ⌊n/2⌋`. -/
theorem summable_trFreshLaw_trClear (n : ℕ) (e : ℤ × ℤ) (g : ℕ) (hP : pStar ≤ n / 2) :
    Summable fun a : trClear n ↦ trFreshLaw n e g a :=
  summable_trFreshLaw_of_tsum_ofReal_ne_top
    ((tsum_trFreshLaw_trClear_lt n e g hP).trans ENNReal.ofReal_lt_top).ne

/-- **Failed clearing is rare**, real form: if `P_* ≤ ⌊n/2⌋`, then
`∑_{a ∈ Clr} μ_{e,g}(a) < 2^{-43}`. -/
theorem tsum_trFreshLaw_trClear_lt_real (n : ℕ) (e : ℤ × ℤ) (g : ℕ) (hP : pStar ≤ n / 2) :
    ∑' a : trClear n, trFreshLaw n e g a < (2 : ℝ) ^ (-43 : ℤ) := by
  have h := tsum_trFreshLaw_trClear_lt n e g hP
  rwa [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _)
    (summable_trFreshLaw_trClear n e g hP), ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h

end CollatzPosDens
