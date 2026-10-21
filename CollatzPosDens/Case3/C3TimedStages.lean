/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3SmallNextStop
public import CollatzPosDens.Case3.C3StageEnd
public import CollatzPosDens.Case3.C3StageTimes
public import CollatzPosDens.StoppingTrace.TrSurvivalFirstHit

/-!
# Stages are completed on schedule

Let `ι ∈ 𝔍` be a Fourier index, `J = ⌊n/2⌋`, let `ξ ∈ G_n` be a unit, and let black, `gap` and
the stopping sequence refer to `(n, ξ, ε_*)`. Let `e ∈ 𝒫` and `m ∈ ℕ` with `j(e) + m = J`, and
assume `P_*(ι) ≤ J`. Fix `G ≥ 0`, `d ≥ 1`, `k ≥ 1`, write `𝔱_s = 𝔱^{G,d}_s(ι)` for the stage
deadlines and `h = h^st_G(ι)`, and let `C, H` be integers with `H ≤ P_*(ι) - 1`,
`𝔱_s + (d - 1) h ≤ C` and `𝔱_{s+1} ≤ H` for every `0 ≤ s < k`. Let `a = ((r, ℓ), β) ∈ 𝒜_n`
with `β` live, `a ∈ Low^e(ι) \ (Bad^e_m(ι) ∪ Clr(ι))`, and no oversize hit for `ι` at any time
`0 ≤ u ≤ C`. Then the sequence `y = (y^e_u(a))_u` has `se^{G,d}_{k,d}(y; 1) ≤ ν(y)` and
`τ_{se^{G,d}_{k,d}(y;1)}(y) ≤ H`.

The proof shows by induction on `s ≤ k` that some `1 ≤ i_s ≤ ν(y)` has `τ_{i_s}(y) ≤ 𝔱_s` and
`se_{k,d}(1) = se_{k-s,d}(i_s)`. The first hit gives `i_0 = 1`. From stage `s` to `s + 1`, the
state `(k - s, t)` of the stage moves at the stop `w = τ_i(y)`: if `gap(y_w) < G` and `t ≥ 2`,
`CollatzPosDens.exists_bkBlack_trFreshPath_bkColTop_lt_of_trGap_lt` gives the next stop within
`h` steps and the state becomes `(k - s, t - 1)`; otherwise the stage is complete, and the next
stop comes within `h` steps (small gap) or by time `𝔤_ι(w) ≤ 𝔣^{G,d}_ι(𝔱_s) = 𝔱_{s+1}` (large
gap, by `CollatzPosDens.exists_bkBlack_trFreshPath_bkColTop_lt`, as `w ≤ 𝔱_s + (d - 1) h ≤ C`).
Starting from `t = d`, at most `d - 1` small steps occur, each adding at most `h`, so every stop
of the stage is at most `𝔱_s + d h ≤ 𝔱_{s+1}`.

## Main results

* `CollatzPosDens.trStageEnd_le_trNu_and_trStopTime_le`: the stage end index
  `se^{G,d}_{k,d}(y; 1)` is a natural number `i ≤ ν(y)`, and `τ_i(y) ≤ H`.

## Implementation notes

The stage end index lies in `ℕ∞`; the conclusion `se^{G,d}_{k,d}(y; 1) ≤ ν(y)` together with
`τ_{se}(y) ≤ H` is stated as: `se^{G,d}_{k,d}(y; 1) = i` for some `i ∈ ℕ` with `i ≤ ν(y)` and
`τ_i(y) = some t` with `t ≤ H`. The integers `G ≥ 0`, `d ≥ 1`, `k ≥ 1` are natural numbers, and
the gap threshold enters the stage end index as the integer `G`. The hypotheses `n ≥ 1` and
`C ≤ p_{r_*(ι)}(ι)` are not needed and are not assumed.

## References

* [Mazur, *Collatz positive density*], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `τ_i(x) = w` is defined and some `c < ⌊n/2⌋` with `w < c` is a hit of `x` after `w`,
then `τ_{i+1}(x)` is defined and at most `c`. -/
private theorem exists_trStopTime_succ_le_of_isTrHitAfter {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {x : ℕ → ℤ × ℤ} {i w c : ℕ} (hi : 1 ≤ i) (hw : trStopTime n ξ ε x i = some w)
    (hcJ : c < n / 2) (hwc : w < c) (hhit : IsTrHitAfter n ξ ε x w c) :
    ∃ w', trStopTime n ξ ε x (i + 1) = some w' ∧ w' ≤ c := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  rcases ht : trStopTime n ξ ε x (i + 2) with _ | t
  · exact absurd hhit ((trStopTime_succ_succ_eq_none_iff hw).1 ht c hcJ hwc)
  · refine ⟨t, rfl, ?_⟩
    obtain ⟨q', hq', -, -, hmin⟩ := trStopTime_succ_succ_eq_some_iff.1 ht
    rw [hw, Option.some_inj] at hq'
    subst hq'
    exact not_lt.1 fun hlt => hmin c hlt ⟨hwc, hhit⟩

/-- **Stages are completed on schedule.** Let `ι ∈ 𝔍`, `J = ⌊n/2⌋`, `ξ ∈ G_n` a unit, `e ∈ 𝒫`
and `m ∈ ℕ` with `j(e) + m = J` and `P_*(ι) ≤ J`. Let `G ≥ 0`, `d ≥ 1`, `k ≥ 1`, and `C, H`
integers with `H ≤ P_*(ι) - 1`, `𝔱^{G,d}_s(ι) + (d - 1) h^st_G(ι) ≤ C` and
`𝔱^{G,d}_{s+1}(ι) ≤ H` for every `0 ≤ s < k`. Let `a = ((r, ℓ), β)` with `β` live,
`a ∈ Low^e(ι) \ (Bad^e_m(ι) ∪ Clr(ι))`, and no oversize hit for `ι` at any time `0 ≤ u ≤ C`.
Then, for `y = (y^e_u(a))_u`, the stage end index `se^{G,d}_{k,d}(y; 1)` is a natural number
`i ≤ ν(y)`, and `τ_i(y) ≤ H`; everything refers to `(n, ξ, ε_*)`. -/
@[collatz_pos_dens "lem_c3_timed_stages"]
theorem trStageEnd_le_trNu_and_trStopTime_le {ι : FIndex} {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {e : ℤ × ℤ} (he : e ∈ bkPoints) {m : ℕ}
    (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ)) (hP : pStar ι ≤ n / 2) {G d k : ℕ} (hd : 1 ≤ d)
    (hk : 1 ≤ k) {C H : ℤ} (hH : H ≤ (pStar ι : ℤ) - 1)
    (hC : ∀ s < k, ((trStageTime ι G d s + (d - 1) * trStageHold ι G : ℕ) : ℤ) ≤ C)
    (hHs : ∀ s < k, (trStageTime ι G d (s + 1) : ℤ) ≤ H)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hlive : TrLive a.2) (hlow : a ∈ trLow ι n ξ e)
    (hbad : a ∉ trBad ι n e m) (hclr : a ∉ trClear ι n)
    (hover : ∀ u : ℕ, (u : ℤ) ≤ C → ¬IsTrOversizeHit ι n ξ (epsStar : ℝ) e a u) :
    ∃ i : ℕ, trStageEnd n ξ (epsStar : ℝ) (G : ℤ) d (trFreshPath e a) k d 1 = i ∧
      i ≤ trNu n ξ (epsStar : ℝ) (trFreshPath e a) ∧
      ∃ t, trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) i = some t ∧ (t : ℤ) ≤ H := by
  set y := trFreshPath e a with hy
  set se := trStageEnd n ξ (epsStar : ℝ) (G : ℤ) d y with hse
  obtain ⟨h, hh⟩ : ∃ h, trStageHold ι G = h := ⟨_, rfl⟩
  rw [hh] at hC
  have stage : ∀ s < k, ∀ κ, 1 ≤ κ → ∀ t, 1 ≤ t → t ≤ d → ∀ i w, 1 ≤ i →
      trStopTime n ξ (epsStar : ℝ) y i = some w → w + t * h ≤ trStageTime ι G d s + d * h →
      ∃ i' w', 1 ≤ i' ∧ trStopTime n ξ (epsStar : ℝ) y i' = some w' ∧
        w' ≤ trStageTime ι G d (s + 1) ∧ se κ t i = se (κ - 1) d i' := by
    intro s hs κ hκ t
    have hstep : trStageTime ι G d s + d * h ≤ trStageTime ι G d (s + 1) := by
      rw [trStageTime_succ, ← hh]
      exact add_mul_le_trStageMap ι G d _
    have hgmap : recipeMap ι (trStageTime ι G d s + (d - 1) * h) ≤
        trStageTime ι G d (s + 1) := by
      rw [trStageTime_succ, ← hh]
      exact recipeMap_le_trStageMap ι G d _
    have hCs := hC s hs
    have hHs' := hHs s hs
    have hPs : trStageTime ι G d (s + 1) ≤ pStar ι - 1 := by omega
    obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
    simp only [Nat.add_sub_cancel] at hgmap hCs
    induction t with
    | zero => intro h0; omega
    | succ t ih =>
      intro _ htd i w hi hw hwt
      have hwb : BkBlack n ξ (epsStar : ℝ) (y w) := isTrHit_of_trStopTime_eq_some hw
      have hrec := trStageEnd_of_trStopTime_eq_some (G := (G : ℤ)) (d := d' + 1) hκ (t + 1) hw
      rw [← hse] at hrec
      have hwh : w + h ≤ trStageTime ι G (d' + 1) s + (d' + 1) * h := by nlinarith
      have hwd : w ≤ trStageTime ι G (d' + 1) s + d' * h := by nlinarith
      by_cases hg : (G : ℤ) ≤ trGap n ξ (epsStar : ℝ) (y w)
      · rw [trStageNext_of_le hg] at hrec
        have hwC : (w : ℤ) ≤ C := by omega
        have hgw : recipeMap ι w ≤ trStageTime ι G (d' + 1) (s + 1) :=
          (recipeMap_le_of_le ι hwd).trans hgmap
        obtain ⟨c, hwc, hcg, hcJ, hcb, hctop⟩ :=
          exists_bkBlack_trFreshPath_bkColTop_lt (ι := ι) hξ he hm hP hlive hlow hbad hclr
            hwb (hover w hwC) (hgw.trans hPs)
        obtain ⟨w', hw', hw'c⟩ :=
          exists_trStopTime_succ_le_of_isTrHitAfter hi hw hcJ hwc ⟨hcb, hctop⟩
        exact ⟨i + 1, w', by omega, hw', by omega, hrec⟩
      · push Not at hg
        obtain ⟨c, hwc, hch, hcJ, hcb, hctop⟩ :=
          exists_bkBlack_trFreshPath_bkColTop_lt_of_trGap_lt hm hP hlive hlow hbad
            (G := G) (q := w) (by rw [hh]; omega) hg
        rw [hh] at hch
        obtain ⟨w', hw', hw'c⟩ :=
          exists_trStopTime_succ_le_of_isTrHitAfter hi hw hcJ hwc ⟨hcb, hctop⟩
        rcases Nat.lt_or_ge t 1 with ht | ht
        · obtain rfl : t = 0 := by omega
          rw [trStageNext_one] at hrec
          exact ⟨i + 1, w', by omega, hw', by omega, hrec⟩
        · rw [trStageNext_of_lt hg (by omega)] at hrec
          simp only [Nat.add_sub_cancel] at hrec
          obtain ⟨i', w'', hi', hw'', hle, heq⟩ :=
            ih ht (by omega) (i + 1) w' (by omega) hw' (by nlinarith)
          exact ⟨i', w'', hi', hw'', hle, hrec.trans heq⟩
  have key : ∀ s ≤ k, ∃ i w, 1 ≤ i ∧ trStopTime n ξ (epsStar : ℝ) y i = some w ∧
      w ≤ trStageTime ι G d s ∧ se k d 1 = se (k - s) d i := by
    intro s
    induction s with
    | zero =>
      intro _
      obtain ⟨c, -, hc0, hcJ, hc⟩ :=
        exists_bkBlack_trFreshPath_of_mem_trLow_diff_trBad hm hP ⟨hlow, hbad⟩
      rcases ht : trStopTime n ξ (epsStar : ℝ) y 1 with _ | t
      · exact absurd hc ((trStopTime_one_eq_none_iff.1 ht) c hcJ)
      · refine ⟨1, t, le_rfl, ht, ?_, by simp⟩
        rw [trStageTime_zero]
        exact (not_lt.1 fun hlt => (trStopTime_one_eq_some_iff.1 ht).2.2 c hlt hc).trans hc0
    | succ s ih =>
      intro hsk
      obtain ⟨i, w, hi, hw, hws, heq⟩ := ih (by omega)
      have hwd : w + d * h ≤ trStageTime ι G d s + d * h := by omega
      obtain ⟨i', w', hi', hw', hws', heq'⟩ :=
        stage s (by omega) (k - s) (by omega) d hd le_rfl i w hi hw hwd
      refine ⟨i', w', hi', hw', hws', heq.trans ?_⟩
      rw [heq', show k - s - 1 = k - (s + 1) by omega]
  obtain ⟨i, w, hi, hw, hwk, heq⟩ := key k le_rfl
  rw [Nat.sub_self] at heq
  refine ⟨i, heq.trans (trStageEnd_zero _ _), ?_, w, hw, ?_⟩
  · exact (isSome_trStopTime_iff.1 (by rw [hw]; rfl)).2
  · have := hHs (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at this
    omega

end CollatzPosDens
