/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageMass
public import CollatzPosDens.Case3.C3StageMoment
public import CollatzPosDens.Case3.C3StageShift
public import CollatzPosDens.StoppingTrace.TrMomentBlack

/-!
# Stage moments from a black origin

Fix a level `n`, put `J = ⌊n/2⌋` and fix a residue `ξ ∈ G_n`; a point `v` is black when
`CollatzPosDens.BkBlack n ξ ε_* v` holds. For a black point `v ∈ 𝒫`, `N ∈ ℕ` with `j(v) + N > J`,
and all `G`, `d`, `k`, `t`, the discount at the end of the stages, averaged over `β ∈ 𝔅^N` against
the block-list weight `bw^⊗`, is the stopped-stage mass:
```
∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵^{G,d}_{k,t}(v, β) = 𝓜^{G,d}_{k,t}(v).
```
The proof is by induction on `(k, t)` in the lexicographic order, for all black `v` and all
admissible `N` at once. From a black origin the first stop of every path is at time `0`. For
`k = 0` the stage end index is `1`, so `𝒵^{G,d}_{0,t}(v, β) = 1`, and the sum is the total mass
`1` of `𝔅^N`. For `k ≥ 1`, with `(k', t') = nx_{G,d}(k, t; gap(v))`, the stage end index from the
first stop is the index `se^{G,d}_{k',t'}(x; 2)` from the second; the second stop `q = τ_2(x)` of a
live `β` is the length of the unique prefix `u = β_{[1,q]}` lying in the set `𝓔(v)` of entry
lists, and restarting the stopping sequence at `q` (`CollatzPosDens.trStopTime_trPath_restart`,
`CollatzPosDens.trStageEnd_add_of_shift` with `c = 1`) factors
`𝒵^{G,d}_{k,t}(v, β) = e^{-γ_* N^*(v, u; q)} 𝒵^{G,d}_{k',t'}(x_q(v, u), β_{[q+1,N]})`. Splitting
the sum over `β` at `q` turns the inner sum into `𝓜^{G,d}_{k',t'}(x_q(v, u))` by induction, and
the recursion of the masses closes the step.

## Main results

* `CollatzPosDens.tsum_trListWeight_mul_trStageMoment_eq_trStageMass`: the identity above.

## Implementation notes

The sum is the unconditional sum in `[0, ∞]`, the real numbers `bw^⊗(β)` and
`𝒵^{G,d}_{k,t}(v, β)` entering through `ENNReal.ofReal`; both are nonnegative, so nothing is
truncated. The set `𝔅^N` is the subtype of lists of `N` blocks whose closing letters lie in
`{4, 5}`. The identity holds without the hypotheses `n ≥ 1`, `ξ` a unit, `G ≥ 0`, `d ≥ 1` and
`1 ≤ t ≤ d`; `J ≥ 1` follows from `v ∈ 𝒫` being black.

## References

* [Mazur, *Collatz positive density*], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n} {G : ℤ} {d : ℕ}

/-- From a black origin the first stop is at time `0`. -/
private theorem trStopTime_one_eq_some_zero_of_bkBlack {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hvb : BkBlack n ξ (epsStar : ℝ) v) (β : List (List ℤ × ℤ)) :
    trStopTime n ξ (epsStar : ℝ) (trPath v β) 1 = some 0 := by
  have hJ : 0 < n / 2 := by
    have h1 := hvb.bkJ_le
    have h2 : (1 : ℤ) ≤ bkJ v := hv
    omega
  exact trStopTime_one_eq_some_iff.2 ⟨hJ, by simpa [isTrHit_iff] using hvb,
    fun s hs => absurd hs (Nat.not_lt_zero s)⟩

/-- From a black origin no stage has to be completed in the empty run:
`𝒵^{G,d}_{0,t}(v, β) = 1`. -/
theorem trStageMoment_zero_of_bkBlack {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hvb : BkBlack n ξ (epsStar : ℝ) v) (t : ℕ) (β : List (List ℤ × ℤ)) :
    trStageMoment n ξ G d 0 t v β = 1 := by
  rw [trStageMoment_eq_of_trStopTime_eq_some (trStageEnd_zero t 1)
    (trStopTime_one_eq_some_zero_of_bkBlack hv hvb β), trCount_zero, mul_zero, neg_zero,
    Real.exp_zero]

/-- From a black origin, the stage end index with `k + 1` stages from the first stop is the index
at the next state from the second stop. -/
private theorem trStageEnd_succ_one_of_bkBlack {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hvb : BkBlack n ξ (epsStar : ℝ) v) (β : List (List ℤ × ℤ)) (k t : ℕ) :
    trStageEnd n ξ (epsStar : ℝ) G d (trPath v β) (k + 1) t 1 =
      trStageEnd n ξ (epsStar : ℝ) G d (trPath v β)
        (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).1
        (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).2 2 := by
  rw [trStageEnd_of_trStopTime_eq_some (Nat.le_add_left 1 k) t
    (trStopTime_one_eq_some_zero_of_bkBlack hv hvb β), trPath_zero]

/-- The discount `𝒵^{G,d}_{k+1,t}(v, β)` of a live list from a black origin, decomposed at the
second stop over the entry lists `β_{[1,q]} ∈ 𝓔(v)`. -/
theorem ofReal_trStageMoment_succ_eq_sum {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hvb : BkBlack n ξ (epsStar : ℝ) v) (β : List (List ℤ × ℤ))
    (hβ : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)) (hlive : TrLive β)
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ v + β.length) (k t : ℕ) :
    ENNReal.ofReal (trStageMoment n ξ G d (k + 1) t v β) =
      ∑ q ∈ Finset.range (β.length + 1), (trEntryWords n ξ (epsStar : ℝ) v).indicator
        (fun u => ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ v u q))) *
          ENNReal.ofReal (trStageMoment n ξ G d
            (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).1
            (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).2
            (trPath v u q) (trSublist β (q + 1) β.length)))
        (trSublist β 1 q) := by
  set k' := (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).1
  set t' := (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).2
  have hse := trStageEnd_succ_one_of_bkBlack (G := G) (d := d) hv hvb β k t
  have hpre := trStopTime_two_eq_some_iff_trSublist_mem_trEntryWords hv hvb β hβ hlive hN
  have hstop : ∀ q ∈ Finset.range (β.length + 1),
      trSublist β 1 q ∈ trEntryWords n ξ (epsStar : ℝ) v →
        2 ≤ trNu n ξ (epsStar : ℝ) (trPath v β) ∧
          trStopTime n ξ (epsStar : ℝ) (trPath v β) 2 = some q := by
    intro q hq hu
    have hqN : q ≤ β.length := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    have hlen : (trSublist β 1 q).length = q := by simp [hqN]
    exact (hpre q).2 ⟨hlen ▸ trEntryWords_length_pos hu, hqN, hu⟩
  by_cases hex : ∃ q, 2 ≤ trNu n ξ (epsStar : ℝ) (trPath v β) ∧
      trStopTime n ξ (epsStar : ℝ) (trPath v β) 2 = some q
  · obtain ⟨q, hq⟩ := hex
    obtain ⟨hq1, hqN, hu⟩ := (hpre q).1 hq
    rw [Finset.sum_eq_single_of_mem q (Finset.mem_range.2 (by omega)) fun q' hq' hne =>
      Set.indicator_of_notMem (fun hu' => hne (Option.some_inj.1
        ((hstop q' hq' hu').2.symm.trans hq.2))) _, Set.indicator_of_mem hu]
    obtain ⟨hres, hν⟩ := trStopTime_trPath_restart hv hN hq.2
    have happ : trSublist β 1 q ++ trSublist β (q + 1) β.length = β := by
      rw [trSublist_append_trSublist β le_rfl (by omega) hqN, trSublist_one_length]
    have hulen : (trSublist β 1 q).length = q := by simp [hqN]
    have hx : trPath v (trSublist β 1 q) q = trPath v β q := by
      conv_rhs => rw [← happ]
      rw [trPath_concat v _ _ hulen.ge]
    rw [hx]
    set x' := trPath (trPath v β q) (trSublist β (q + 1) β.length)
    have hshift : ∀ w, trPath v β (q + w) = x' w := fun w => by
      conv_lhs => rw [← happ]
      rw [trPath_append_add v _ _ hulen w, hx]
    have hν' : trNu n ξ (epsStar : ℝ) (trPath v β) = 1 + trNu n ξ (epsStar : ℝ) x' := hν
    have hτ : ∀ i, 1 ≤ i → i ≤ trNu n ξ (epsStar : ℝ) x' →
        trStopTime n ξ (epsStar : ℝ) (trPath v β) (1 + i) =
          (trStopTime n ξ (epsStar : ℝ) x' i).map (q + ·) := fun i hi _ => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
      rw [show 1 + (m + 1) = 2 + m by omega]
      exact hres m
    have hse2 := trStageEnd_add_of_shift (G := G) (d := d) hshift hν' hτ k' t' 1 le_rfl
    rw [hse2] at hse
    have h1 := le_trStageEnd (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (G := G) (d := d) (x := x')
      k' t' 1
    cases hi : trStageEnd n ξ (epsStar : ℝ) G d x' k' t' 1 using ENat.recTopCoe with
    | top =>
      rw [hi, add_top] at hse
      rw [trStageMoment_eq_zero_of_eq_top hse, trStageMoment_eq_zero_of_eq_top hi]
      simp
    | coe i =>
      rw [hi] at hse h1
      have hi1 : 1 ≤ i := by exact_mod_cast h1
      have hse' : trStageEnd n ξ (epsStar : ℝ) G d (trPath v β) (k + 1) t 1 = ((1 + i : ℕ) : ℕ∞) :=
        by rw [hse]; push_cast; rfl
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi1
      have hτm := hres m
      rw [show 2 + m = 1 + (m + 1) by omega] at hτm
      cases hs : trStopTime n ξ (epsStar : ℝ) x' (m + 1) with
      | none =>
        rw [hs, Option.map_none] at hτm
        rw [trStageMoment_eq_zero_of_trStopTime_eq_none hse' hτm,
          trStageMoment_eq_zero_of_trStopTime_eq_none hi hs]
        simp
      | some s =>
        rw [hs, Option.map_some] at hτm
        rw [trStageMoment_eq_of_trStopTime_eq_some hse' hτm,
          trStageMoment_eq_of_trStopTime_eq_some hi hs]
        have hc := trCount_concat ξ v (trSublist β 1 q) (trSublist β (q + 1) β.length) hulen s
        rw [happ, hx] at hc
        rw [hc, mul_add, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  · rw [Finset.sum_eq_zero fun q hq =>
      Set.indicator_of_notMem (fun hu' => hex ⟨q, hstop q hq hu'⟩) _]
    have hν2 : trNu n ξ (epsStar : ℝ) (trPath v β) < 2 := by
      by_contra h2
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1
        (isSome_trStopTime_iff (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (x := trPath v β)
          (i := 2) |>.2 ⟨by norm_num, by omega⟩)
      exact hex ⟨q, by omega, hq⟩
    have h2 := le_trStageEnd (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (G := G) (d := d)
      (x := trPath v β) k' t' 2
    rw [← hse] at h2
    rw [trStageMoment_eq_zero_of_trNu_lt (lt_of_lt_of_le (by exact_mod_cast hν2) h2),
      ENNReal.ofReal_zero]

/-- **Stage moments from a black origin.** Let `v ∈ 𝒫` be black for `(n, ξ, ε_*)`, and let
`N ∈ ℕ` with `j(v) + N > ⌊n/2⌋`. Then for all `G`, `d`, `k` and `t`,
`∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵^{G,d}_{k,t}(v, β) = 𝓜^{G,d}_{k,t}(v)`. -/
@[collatz_pos_dens "lem_c3_stage_moment_black"]
theorem tsum_trListWeight_mul_trStageMoment_eq_trStageMass (G : ℤ) (d : ℕ) :
    ∀ (k t : ℕ) {v : ℤ × ℤ}, v ∈ bkPoints → BkBlack n ξ (epsStar : ℝ) v →
    ∀ {N : ℕ}, ((n / 2 : ℕ) : ℤ) < bkJ v + N →
    ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (trStageMoment n ξ G d k t v β.1) =
      trStageMass n ξ G d k t v
  | 0, t, v, hv, hvb, N, _ => by
    simp only [trStageMoment_zero_of_bkBlack hv hvb, ENNReal.ofReal_one, mul_one,
      trStageMass_zero]
    exact tsum_ofReal_trListWeight_length_eq N
  | k + 1, t, v, hv, hvb, N, hN => by
    set k' := (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).1
    set t' := (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).2
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → List (List ℤ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞, ∀ q u f,
        Ψ q u f = (trEntryWords n ξ (epsStar : ℝ) v).indicator (fun u =>
          ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ v u q))) *
            ENNReal.ofReal (trStageMoment n ξ G d k' t' (trPath v u q) f)) u :=
      ⟨_, fun _ _ _ => rfl⟩
    have hL : ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) *
            ENNReal.ofReal (trStageMoment n ξ G d (k + 1) t v β.1) =
        ∑ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) *
            Ψ q (trSublist β.1 1 q) (trSublist β.1 (q + 1) N) := by
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr fun β => ?_
      obtain ⟨hlen, hβ⟩ := β.2
      rw [← Finset.mul_sum]
      by_cases hlive : TrLive β.1
      · have h := ofReal_trStageMoment_succ_eq_sum (G := G) (d := d) hv hvb β.1 hβ hlive
          (by rw [hlen]; exact hN) k t
        rw [hlen] at h
        simp only [h, hΨ]
        rfl
      · simp [trListWeight_eq_zero_of_not_trLive hlive]
    have hG : ∀ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) * Ψ q (trSublist β.1 1 q) (trSublist β.1 (q + 1) N) =
        ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)},
          (trEntryWords n ξ (epsStar : ℝ) v).indicator (fun u =>
            ENNReal.ofReal (trListWeight u) *
              ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length)) *
                trStageMass n ξ G d k' t' (trPath v u u.length)) u.1 := by
      intro q hq
      obtain ⟨b, rfl⟩ : ∃ b, N = q + b := ⟨N - q, by have := Finset.mem_range.1 hq; omega⟩
      refine (tsum_trListWeight_trSublist {c : List ℤ × ℤ | c.2 ∈ ({4, 5} : Set ℤ)} q b
        (Ψ q)).trans (tsum_congr fun u => ?_)
      obtain ⟨u, rfl, -⟩ := u
      by_cases hu : u ∈ trEntryWords n ξ (epsStar : ℝ) v
      · simp only [hΨ, Set.indicator_of_mem hu]
        have := bkJ_add_length_le_bkJ_trPath v u
        rw [← tsum_trListWeight_mul_trStageMoment_eq_trStageMass G d k' t'
          (trPath_mem_bkPoints hv u _) (trEntryWords_bkBlack hu) (N := b)
          (by push_cast at hN; omega), ← ENNReal.tsum_mul_left]
        exact tsum_congr fun f => by rw [neg_mul]; ring
      · simp only [hΨ, Set.indicator_of_notMem hu, mul_zero, tsum_zero]
    rw [hL, Finset.sum_congr rfl hG, sum_range_tsum_indicator_eq_tsum (N := N) _ _
      fun u hu => ⟨length_lt_of_mem_trEntryWords hN hu, fun b hb => trEntryWords_closing_mem hu hb⟩,
      trStageMass_succ]
termination_by k t => (k, t)
decreasing_by exact trStageNext_lt (Nat.le_add_left 1 k)

end CollatzPosDens
