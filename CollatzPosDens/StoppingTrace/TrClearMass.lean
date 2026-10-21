/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnListMarginal
public import CollatzPosDens.StoppingTrace.TrClear
public import CollatzPosDens.StoppingTrace.TrFreshMarginal
public import CollatzPosDens.StoppingTrace.TrRecipeIterMono
public import CollatzPosDens.StoppingTrace.TrVerLowClear
public import CollatzPosDens.Transfer.S02Beta
public import CollatzPosDens.Transfer.S02ClearCount
public import CollatzPosDens.Transfer.S02ClearExp
public import CollatzPosDens.Transfer.S02ClearExpPos
public import CollatzPosDens.Transfer.S02Epiece
public import CollatzPosDens.Transfer.S02TraceIndex
public import CollatzPosDens.Transfer.S02Ycl
public import CollatzPosDens.Transfer.S02Vcl
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The full clearing allowance

Let `ι ∈ 𝔍` be a Fourier index, `J = ⌊n/2⌋`, and suppose `P_*(ι) ≤ J`. Under the fresh law
`μ_{e,g}`, the slow clearing event `Clr(ι)` has mass `μ_{e,g}(Clr(ι)) ≤ E_piece(ι)`, the clearing
allowance.

Write `P_* = P_*(ι)`, `r_* = r_*(ι)`, `p_i = p_i(ι)`, `S_i = S_i(ι)`, `h_*(u) = h_*(ι, u)`,
`β_*(u) = β_*(ι, u)`, `i_*(u) = i_*(ι, u)`, `t^cl_i = t^cl_i(ι)` and `n^cl_i = n^cl_i(ι)`.
Write `y = y_cl(ι)` for the clearing point and `v = v_cl(ι)` for the clearing exponent, so that
`(y, v) = (8191/8192, 1279/100)` for `ι = o` and `(y, v) = (255/256, 25/2)` for `ι = b`; in both
cases `0 < y < 1`.

For a window `{u + 1, …, u + h}` with `u + h ≤ J` and a threshold `Y`, the atoms whose blocks
gain at most `Y` over the window have mass at most `y^{v h - Y}`: by the displacement
marginal of the fresh law and `∑ F_g ≤ 1`, the mass is at most the `η^{⊗(u+h)}`-mass of the hold
lists whose last `h` entries have total height at most `Y`; the first `u` entries contribute a
factor `1`, and the lower vertical tail of `η^{⊗h}` at the clearing point gives the bound.

For an admissible window, `u + h_*(u) ≤ P_* - 1 = p_{r_*}`, so `i = i_*(u)` is defined by the
schedule and `a_i ≤ u ≤ p_i`; as the schedule is strictly increasing, `i_*(p_i) = i`, whence
`β_*(u) = S_i` and `h_*(u) = h_*(p_i)`. The exponent `v h_*(u) - (13/9) β_*(u)` is then
`t^cl_i / (1 - y)`, and since `log y ≤ -(1 - y)` and `P_80(t) ≤ e^t` for `t ≥ 0`, the window `u`
contributes at most `1 / P_80(t^cl_i)`. Grouping the admissible windows by their trace index,
there are at most `n^cl_i` of them with index `i`, and the union bound gives
`μ_{e,g}(Clr(ι)) ≤ ∑_{i=0}^{r_*} n^cl_i / P_80(t^cl_i) ≤ E_piece(ι)`.

## Main results

* `CollatzPosDens.tsum_trFreshLaw_trClearWindow_le`: the mass of a single slow window.
* `CollatzPosDens.tsum_trFreshLaw_trClear_lt`: `μ_{e,g}(Clr(ι)) ≤ E_piece(ι)`, as a sum in
  `[0, ∞]`.
* `CollatzPosDens.summable_trFreshLaw_trClear`: the fresh law is summable on `Clr(ι)`.
* `CollatzPosDens.tsum_trFreshLaw_trClear_lt_real`: `μ_{e,g}(Clr(ι)) ≤ E_piece(ι)`, as a real
  sum.

## Implementation notes

The mass `μ_{e,g}(Clr(ι))` is the unconditional sum over the subtype `Clr` of
`ENNReal.ofReal (trFreshLaw n e g a)`, as in the displacement marginal of the fresh law; this
form needs no summability assumption, and the real form follows. The hypotheses `n ≥ 1`, that
`ξ ∈ G_n` is a unit and that `e ∈ 𝒫` play no role in the bound and are dropped; only
`P_*(ι) ≤ ⌊n/2⌋` is used, to place every admissible window inside the block list.

## References

* [Mazur, *Collatz positive density*], §9.13.
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
`η^{⊗(q+h)}`-mass at most `y_cl(ι)^{v_cl(ι) h - Y}`. -/
private lemma trClearMass_hold_window (ι : FIndex) (q h : ℕ) (Y : ℝ) :
    ∑' u : {u : Fin (q + h) → ℕ × ℤ //
        (∀ i, 1 ≤ (u i).1) ∧ ∑ i : Fin h, ((u (Fin.natAdd q i)).2 : ℝ) ≤ Y},
      ENNReal.ofReal (holdListLaw u.1) ≤
        ENNReal.ofReal ((clearingPoint ι : ℝ) ^ ((clearingPower ι : ℝ) * h - Y)) := by
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
      ENNReal.ofReal ((clearingPoint ι : ℝ) ^ ((clearingPower ι : ℝ) * h - Y)) := by
    rw [← tsum_subtype B (fun u ↦ ENNReal.ofReal (holdListLaw u))]
    exact tsum_holdListLaw_verLowClear_le ι h Y
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

/-- **Mass of a slow window.** If `q + h ≤ ⌊n/2⌋`, the fresh atoms whose blocks gain at most
`Y` over the window `{q + 1, …, q + h}` have `μ_{e,g}`-mass at most `y_cl(ι)^{v_cl(ι) h - Y}`,
for each Fourier index `ι`. -/
theorem tsum_trFreshLaw_trClearWindow_le (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (g q h : ℕ) (Y : ℝ)
    (hq : q + h ≤ n / 2) :
    ∑' a : {a | a ∈ trAtoms n ∧ (trClearGain a.2 q h : ℝ) ≤ Y},
        ENNReal.ofReal (trFreshLaw n e g a) ≤
      ENNReal.ofReal ((clearingPoint ι : ℝ) ^ ((clearingPower ι : ℝ) * h - Y)) := by
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
  set B := ENNReal.ofReal ((clearingPoint ι : ℝ) ^ ((clearingPower ι : ℝ) * h - Y))
  have hinner : ∀ rl : ℕ × ℤ, ∑' h' : {h' : Fin (q + h) → ℤ × ℤ // ∀ i, h' i ∈ bkPoints},
      ENNReal.ofReal (holdListLaw fun i ↦ ((h'.1 i).1.toNat, (h'.1 i).2)) * G rl h'.1 ≤ B :=
    fun rl ↦ (tsum_holdListLaw_bkPoints_mul_indicator_le ψ
      (fun u ↦ ∑ i : Fin h, ((u (Fin.natAdd q i)).2 : ℝ) ≤ Y) (fun _ _ hh ↦ hh)).trans
      (trClearMass_hold_window ι q h Y)
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

/-- The trace index of a schedule position: `i_*(ι, p_i(ι)) = i` for `i ≤ r_*(ι)`. -/
private lemma trClearMass_traceIndex_schedule (ι : FIndex) {i : ℕ} (hi : i ≤ rStar ι) :
    traceIndex ι (schedule ι i) = i :=
  (traceIndex_eq_iff ι (schedule_monotone ι hi)).2
    ⟨hi, le_rfl, fun _ hj ↦ schedule_le_schedule ι hj hi⟩

/-- `β_*(ι, ·)` is constant on the schedule blocks: `β_*(ι, p_{i_*(ι,u)}(ι)) = β_*(ι, u)`. -/
private lemma trClearMass_betaStar_schedule (ι : FIndex) (u : ℕ) :
    betaStar ι (schedule ι (traceIndex ι u)) = betaStar ι u := by
  rw [betaStar_def ι, betaStar_def ι,
    trClearMass_traceIndex_schedule ι (traceIndex_le_rStar ι u)]

/-- `h_*(ι, ·)` is constant on the schedule blocks: `h_*(ι, u) = h_*(ι, p_{i_*(ι,u)}(ι))`. -/
private lemma trClearMass_windowLength_eq (ι : FIndex) (u : ℕ) :
    windowLength ι u = windowLength ι (schedule ι (traceIndex ι u)) := by
  rw [windowLength_eq_div ι, windowLength_eq_div ι, trClearMass_betaStar_schedule ι]

/-- Every time lies after the start of its clearing block: `a_{i_*(ι, u)} ≤ u`. -/
private lemma trClearMass_clearStart_le (ι : FIndex) (u : ℕ) :
    clearStart ι (traceIndex ι u) ≤ u := by
  rcases h : traceIndex ι u with _ | j
  · simp
  · have := schedule_lt_of_lt_traceIndex ι (u := u) (j := j) (by omega)
    rw [clearStart_succ ι]
    omega

/-- The exponent bound: for `u ∈ ℕ` and `i = i_*(ι, u)`,
`y_cl(ι)^{v_cl(ι) h_*(ι, u) - (13/9) β_*(ι, u)} ≤ 1 / P_80(t^cl_i(ι))`. -/
private lemma trClearMass_rpow_le (ι : FIndex) (u : ℕ) :
    (clearingPoint ι : ℝ) ^
        ((clearingPower ι : ℝ) * (windowLength ι u : ℝ) - 13 / 9 * (betaStar ι u : ℝ)) ≤
      1 / expPartialSum 80 ((clearingExponent ι (traceIndex ι u) : ℚ) : ℝ) := by
  set i := traceIndex ι u with hi
  set t : ℝ := ((clearingExponent ι i : ℚ) : ℝ) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact_mod_cast (clearingExponent_pos (traceIndex_le_rStar ι u)).le
  set s : ℝ := 1 - (clearingPoint ι : ℝ) with hs
  have hs0 : 0 < s := by
    have : (clearingPoint ι : ℝ) < 1 := by exact_mod_cast clearingPoint_lt_one ι
    linarith
  have hexp : (clearingPower ι : ℝ) * (windowLength ι u : ℝ) - 13 / 9 * (betaStar ι u : ℝ) =
      t / s := by
    rw [ht, clearingExponent_cast ι, trClearMass_windowLength_eq ι u, betaStar_def ι, ← hs,
      mul_div_cancel_left₀ _ hs0.ne']
  have hy0 : (0 : ℝ) < clearingPoint ι := by exact_mod_cast clearingPoint_pos ι
  have hlog : Real.log (clearingPoint ι : ℝ) ≤ -s := by
    have := Real.log_le_sub_one_of_pos hy0
    linarith
  have hP0 : 0 < expPartialSum 80 t := expPartialSum_pos 80 ht0
  have hPexp : expPartialSum 80 t ≤ exp t := by
    rw [expPartialSum]
    exact Real.sum_le_exp_of_nonneg ht0 81
  rw [hexp, Real.rpow_def_of_pos hy0]
  calc exp (Real.log (clearingPoint ι) * (t / s)) ≤ exp (-t) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_right hlog (by positivity : (0 : ℝ) ≤ t / s)
        rwa [neg_mul, mul_div_cancel₀ _ hs0.ne'] at this
    _ = 1 / exp t := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / expPartialSum 80 t := one_div_le_one_div_of_le hP0 hPexp

/-- Each block term of the clearing allowance pays for its clearing count:
`n^cl_i(ι) / P_80(t^cl_i(ι)) ≤ 10^{-24} ⌈10^24 n^cl_i(ι) / P_80(t^cl_i(ι))⌉`. -/
private lemma trClearMass_term_le (ι : FIndex) (i : ℕ) (hi : i ≤ rStar ι) :
    (clearCount ι i : ℝ) * (1 / expPartialSum 80 ((clearingExponent ι i : ℚ) : ℝ)) ≤
      (((⌈10 ^ 24 * (clearCount ι i : ℚ) / expPartialSum 80 (clearingExponent ι i)⌉ : ℚ) /
        10 ^ 24 : ℚ) : ℝ) := by
  have hP := expPartialSum_pos 80 (clearingExponent_pos hi).le
  have hq : (clearCount ι i : ℚ) / expPartialSum 80 (clearingExponent ι i) ≤
      (⌈10 ^ 24 * (clearCount ι i : ℚ) / expPartialSum 80 (clearingExponent ι i)⌉ : ℚ) /
        10 ^ 24 := by
    rw [le_div_iff₀ (by positivity)]
    calc (clearCount ι i : ℚ) / expPartialSum 80 (clearingExponent ι i) * 10 ^ 24
        = 10 ^ 24 * (clearCount ι i : ℚ) / expPartialSum 80 (clearingExponent ι i) := by ring
      _ ≤ _ := Int.le_ceil _
  have hR := (Rat.cast_le (K := ℝ)).2 hq
  rw [Rat.cast_div, Rat.cast_natCast, ratCast_expPartialSum] at hR
  rwa [mul_one_div]

/-- **The full clearing allowance.** Let `ι ∈ 𝔍`. If `P_*(ι) ≤ ⌊n/2⌋`, the slow clearing event
has fresh-law mass `∑_{a ∈ Clr(ι)} μ_{e,g}(a) ≤ E_piece(ι)`, as a sum in `[0, ∞]`. -/
@[collatz_pos_dens "lem_tr_clear_mass"]
theorem tsum_trFreshLaw_trClear_lt (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (g : ℕ)
    (hP : pStar ι ≤ n / 2) :
    ∑' a : trClear ι n, ENNReal.ofReal (trFreshLaw n e g a) ≤ ENNReal.ofReal (ePiece ι : ℝ) := by
  set f : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e g a)
  set Cq : ℕ → Set ((ℕ × ℤ) × List (List ℤ × ℤ)) := fun q ↦
    {a | a ∈ trAtoms n ∧ q + windowLength ι q ≤ pStar ι - 1 ∧
      (trClearGain a.2 q (windowLength ι q) : ℝ) ≤ 13 / 9 * (betaStar ι q : ℝ)} with hCq
  have hU : trClear ι n = ⋃ q, Cq q := by
    ext a
    simp only [mem_trClear, Set.mem_iUnion, hCq, Set.mem_ofPred_eq]
    exact ⟨fun ⟨ha, q, h1, h2⟩ ↦ ⟨q, ha, h1, h2⟩, fun ⟨q, ha, h1, h2⟩ ↦ ⟨ha, q, h1, h2⟩⟩
  have hPs := pStar_def ι
  set c : ℕ → ℝ≥0∞ := fun i ↦
    ENNReal.ofReal (1 / expPartialSum 80 ((clearingExponent ι i : ℚ) : ℝ)) with hc
  set b : ℕ → ℝ≥0∞ := fun q ↦
    if q + windowLength ι q ≤ pStar ι - 1 then c (traceIndex ι q) else 0 with hb
  have hq : ∀ q, ∑' a : Cq q, f a ≤ b q := by
    intro q
    by_cases hqP : q + windowLength ι q ≤ pStar ι - 1
    · have hsub : Cq q ⊆ {a | a ∈ trAtoms n ∧
          (trClearGain a.2 q (windowLength ι q) : ℝ) ≤ 13 / 9 * (betaStar ι q : ℝ)} :=
        fun a ha ↦ ⟨ha.1, ha.2.2⟩
      refine (ENNReal.tsum_mono_subtype f hsub).trans ?_
      refine (tsum_trFreshLaw_trClearWindow_le ι n e g q (windowLength ι q) _ (by omega)).trans ?_
      simp only [hb, hqP, ↓reduceIte]
      exact ENNReal.ofReal_le_ofReal (trClearMass_rpow_le ι q)
    · rw [ENNReal.tsum_eq_zero.2 fun a ↦ absurd a.2.2.1 hqP]
      exact zero_le
  have hsupp : ∀ q ∉ Finset.range (pStar ι), b q = 0 := by
    intro q hq
    rw [Finset.mem_range] at hq
    simp only [hb, ite_eq_right_iff]
    intro h
    omega
  have hmaps : ∀ q ∈ Finset.range (pStar ι), traceIndex ι q ∈ Finset.range (rStar ι + 1) :=
    fun q _ ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (traceIndex_le_rStar ι q))
  have hblock : ∀ i ∈ Finset.range (rStar ι + 1),
      ∑ q ∈ Finset.range (pStar ι) with traceIndex ι q = i, b q ≤
        (clearCount ι i : ℝ≥0∞) * c i := by
    intro i _
    calc ∑ q ∈ Finset.range (pStar ι) with traceIndex ι q = i, b q
        = ∑ q ∈ (Finset.range (pStar ι)).filter (fun q ↦ traceIndex ι q = i) with
            q + windowLength ι q ≤ pStar ι - 1, c i := by
          rw [Finset.sum_filter (fun q ↦ q + windowLength ι q ≤ pStar ι - 1)]
          refine Finset.sum_congr rfl fun q hq ↦ ?_
          simp only [hb]
          rw [(Finset.mem_filter.1 hq).2]
      _ ≤ ∑ q ∈ Finset.Ico (clearStart ι i) (clearStart ι i + clearCount ι i), c i := by
          refine Finset.sum_le_sum_of_subset fun q hq ↦ ?_
          simp only [Finset.mem_filter, Finset.mem_range] at hq
          obtain ⟨⟨hqP, rfl⟩, hqw⟩ := hq
          have hqs : q ≤ schedule ι (rStar ι) := by omega
          have h1 := trClearMass_clearStart_le ι q
          have h2 := le_schedule_traceIndex ι hqs
          have h3 := trClearMass_windowLength_eq ι q
          have h4 := natCast_clearCount ι (traceIndex ι q)
          rw [Finset.mem_Ico]
          omega
      _ = (clearCount ι i : ℝ≥0∞) * c i := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          congr 2
          omega
  have hcast : (ePiece ι : ℝ) = ∑ i ∈ Finset.range (rStar ι + 1),
      (((⌈10 ^ 24 * (clearCount ι i : ℚ) / expPartialSum 80 (clearingExponent ι i)⌉ : ℚ) /
        10 ^ 24 : ℚ) : ℝ) := by
    rw [ePiece_def ι, Rat.cast_sum]
  rw [hU]
  calc ∑' a : ⋃ q, Cq q, f a ≤ ∑' q, ∑' a : Cq q, f a := ENNReal.tsum_iUnion_le_tsum f Cq
    _ ≤ ∑' q, b q := ENNReal.tsum_le_tsum hq
    _ = ∑ q ∈ Finset.range (pStar ι), b q := tsum_eq_sum hsupp
    _ = ∑ i ∈ Finset.range (rStar ι + 1),
          ∑ q ∈ Finset.range (pStar ι) with traceIndex ι q = i, b q :=
        (Finset.sum_fiberwise_of_maps_to hmaps b).symm
    _ ≤ ∑ i ∈ Finset.range (rStar ι + 1), (clearCount ι i : ℝ≥0∞) * c i := Finset.sum_le_sum hblock
    _ ≤ ENNReal.ofReal (ePiece ι : ℝ) := by
        rw [hcast, ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_le_sum fun i hi ↦ ?_
          have hi' : i ≤ rStar ι := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [hc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (trClearMass_term_le ι i hi')
        · intro i hi
          have hi' : i ≤ rStar ι := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          refine le_trans ?_ (trClearMass_term_le ι i hi')
          have := expPartialSum_pos 80
            (show (0 : ℝ) ≤ ((clearingExponent ι i : ℚ) : ℝ) by
              exact_mod_cast (clearingExponent_pos hi').le)
          positivity

/-- The fresh law is summable on the slow clearing event `Clr(ι)`, when `P_*(ι) ≤ ⌊n/2⌋`. -/
theorem summable_trFreshLaw_trClear (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (g : ℕ)
    (hP : pStar ι ≤ n / 2) :
    Summable fun a : trClear ι n ↦ trFreshLaw n e g a :=
  summable_trFreshLaw_of_tsum_ofReal_ne_top
    ((tsum_trFreshLaw_trClear_lt ι n e g hP).trans_lt ENNReal.ofReal_lt_top).ne

/-- **The full clearing allowance**, real form: if `P_*(ι) ≤ ⌊n/2⌋`, then
`∑_{a ∈ Clr(ι)} μ_{e,g}(a) ≤ E_piece(ι)`. -/
theorem tsum_trFreshLaw_trClear_lt_real (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (g : ℕ)
    (hP : pStar ι ≤ n / 2) :
    ∑' a : trClear ι n, trFreshLaw n e g a ≤ (ePiece ι : ℝ) := by
  have h := tsum_trFreshLaw_trClear_lt ι n e g hP
  have h0 : (0 : ℝ) ≤ ePiece ι := by exact_mod_cast ePiece_nonneg ι
  rwa [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trFreshLaw_nonneg _ _ _ _)
    (summable_trFreshLaw_trClear ι n e g hP), ENNReal.ofReal_le_ofReal_iff h0] at h

end CollatzPosDens
