/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Schedule
public import CollatzPosDens.Transfer.S02GMono
public import CollatzPosDens.Transfer.S02GSchedule
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrClear
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrOversizeHit
public import CollatzPosDens.StoppingTrace.TrTrace
public import CollatzPosDens.StoppingTrace.TrNextStop
public import CollatzPosDens.StoppingTrace.TrRecipeIterMono
public import CollatzPosDens.StoppingTrace.TrSurvivalFirstHit

/-!
# Survival: the stops come on schedule

Let `ι ∈ 𝔍` be a Fourier index, `J = ⌊n/2⌋`, let `ξ ∈ G_n` be a unit, and let black and white
refer to `(n, ξ, ε_*)`. Let `e ∈ 𝒫` and `m ∈ ℕ` with `j(e) + m = J`, assume `P_*(ι) ≤ J`, let
`0 ≤ k ≤ r_*(ι)`, and let `a = ((r, ℓ), β) ∈ 𝒜_n` with `β` live and
`a ∈ Low^e(ι) \ (Bad^e_m(ι) ∪ Clr(ι))` have no oversize hit for `ι` at any time `u ≤ p_{k-1}(ι)`
(no condition if `k = 0`). Write `y = (y^e_t(a))_{t ∈ ℕ}`. Then the stopping sequence of `y` has
at least `k + 1` terms, and `τ_i(y) ≤ p_{i-1}(ι)` for `1 ≤ i ≤ k + 1`.

Write `p_i = p_i(ι)`, `r_* = r_*(ι)`, `P_* = P_*(ι)` and `𝔤 = 𝔤_ι`. The proof is by induction
on `i`. The first hit `c ≤ p_0` below `J` bounds `τ_1(y)`. If `q = τ_i(y) ≤ p_{i-1}` with
`i ≤ k`, then `y_q` is black, `q ≤ p_{k-1}` so `a` has no oversize hit at time `q`, and
`𝔤(q) ≤ 𝔤(p_{i-1}) = p_i ≤ p_{r_*} = P_* - 1`; the next stop lemma gives a hit `c` of `y` after
`q` with `q < c ≤ 𝔤(q)` and `c < J`, hence `τ_{i+1}(y)` is defined and at most `c ≤ p_i`.

## Main results

* `CollatzPosDens.le_trNu_and_trStopTime_le_schedule`: the stopping sequence of `y` has at
  least `k + 1` terms and `τ_i(y) ≤ p_{i-1}` for `1 ≤ i ≤ k + 1`.

## Implementation notes

The `i`-th term of the stopping sequence is `trStopTime n ξ ε_* y i : Option ℕ`; the conclusion
records that `k + 1 ≤ ν(y)` and that, for `1 ≤ i ≤ k + 1`, this term is `some t` with
`t ≤ p_{i-1}`. The membership `a ∈ 𝒜_n` is part of `a ∈ Low^e`, and liveness of `β` is
`TrLive a.2`. The oversize-hit hypothesis is stated for `0 < k` only, which is the source's
"no condition if `k = 0`". The hypothesis `n ≥ 1` is not used and is dropped, which generalizes
the source.

## References

* [Mazur, *Collatz positive density*], §9.12.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The trace times come on schedule.** Let `ι ∈ 𝔍`, `J = ⌊n/2⌋`, `ξ ∈ G_n` a unit, `e ∈ 𝒫`
and `m ∈ ℕ` with `j(e) + m = J`, `P_*(ι) ≤ J`, `0 ≤ k ≤ r_*(ι)`, and `a = ((r, ℓ), β)` with `β`
live and `a ∈ Low^e(ι) \ (Bad^e_m(ι) ∪ Clr(ι))` having no oversize hit for `ι` at any time
`u ≤ p_{k-1}(ι)` (no condition if `k = 0`). Then the stopping sequence of `y = (y^e_t(a))_t`
(for `(n, ξ, ε_*)`) has at least `k + 1` terms, and `τ_i(y) ≤ p_{i-1}(ι)` for every
`1 ≤ i ≤ k + 1`. -/
@[collatz_pos_dens "lem_tr_survival_time"]
theorem le_trNu_and_trStopTime_le_schedule {ι : FIndex} {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {e : ℤ × ℤ} (he : e ∈ bkPoints) {m : ℕ}
    (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ))
    (hP : pStar ι ≤ n / 2) {k : ℕ} (hk : k ≤ rStar ι) {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (hlive : TrLive a.2) (hlow : a ∈ trLow ι n ξ e) (hbad : a ∉ trBad ι n e m)
    (hclr : a ∉ trClear ι n)
    (hover : 0 < k → ∀ u ≤ schedule ι (k - 1), ¬IsTrOversizeHit ι n ξ (epsStar : ℝ) e a u) :
    k + 1 ≤ trNu n ξ (epsStar : ℝ) (trFreshPath e a) ∧
      ∀ i, 1 ≤ i → i ≤ k + 1 →
        ∃ t, trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) i = some t ∧
          t ≤ schedule ι (i - 1) := by
  set y := trFreshPath e a
  -- `p_i(ι) ≤ p_{i'}(ι)` for `i ≤ i' ≤ r_*(ι)`
  have hmono : ∀ {i i' : ℕ}, i ≤ i' → i' ≤ rStar ι → schedule ι i ≤ schedule ι i' := by
    intro i i' h hi'
    rcases h.lt_or_eq with h | rfl
    · exact (schedule_le_schedule ι h hi').le
    · exact le_rfl
  have key : ∀ j, j ≤ k →
      ∃ t, trStopTime n ξ (epsStar : ℝ) y (j + 1) = some t ∧ t ≤ schedule ι j := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨c, -, hc0, hcJ, hc⟩ :=
        exists_bkBlack_trFreshPath_of_mem_trLow_diff_trBad hm hP ⟨hlow, hbad⟩
      rcases ht : trStopTime n ξ (epsStar : ℝ) y 1 with _ | t
      · exact absurd hc ((trStopTime_one_eq_none_iff.1 ht) c hcJ)
      · refine ⟨t, rfl, ?_⟩
        exact (not_lt.1 fun hlt => (trStopTime_one_eq_some_iff.1 ht).2.2 c hlt hc).trans hc0
    | succ j ih =>
      intro hjk
      obtain ⟨q, hq, hqle⟩ := ih (by omega)
      have hqb : BkBlack n ξ (epsStar : ℝ) (y q) := isTrHit_of_trStopTime_eq_some hq
      have hqk : q ≤ schedule ι (k - 1) := hqle.trans (hmono (by omega) (by omega))
      have hgq : recipeMap ι q ≤ schedule ι (j + 1) := by
        rw [← recipeMap_schedule ι j (by omega)]
        exact recipeMap_le_of_le ι hqle
      have hgP : recipeMap ι q ≤ pStar ι - 1 := by
        have := hmono (show j + 1 ≤ rStar ι by omega) le_rfl
        rw [pStar_def ι]; omega
      obtain ⟨c, hqc, hcg, hcJ, hcb, hctop⟩ :=
        exists_bkBlack_trFreshPath_bkColTop_lt (ι := ι) hξ he hm hP hlive hlow hbad hclr hqb
          (hover (by omega) q hqk) hgP
      have hhit : IsTrHitAfter n ξ (epsStar : ℝ) y q c := ⟨hcb, hctop⟩
      rcases ht : trStopTime n ξ (epsStar : ℝ) y (j + 2) with _ | t
      · exact absurd hhit ((trStopTime_succ_succ_eq_none_iff hq).1 ht c hcJ hqc)
      · refine ⟨t, rfl, ?_⟩
        obtain ⟨q', hq', -, -, hmin⟩ := trStopTime_succ_succ_eq_some_iff.1 ht
        rw [hq, Option.some_inj] at hq'
        subst hq'
        exact ((not_lt.1 fun hlt => hmin c hlt ⟨hqc, hhit⟩).trans hcg).trans hgq
  refine ⟨?_, fun i hi₁ hik => ?_⟩
  · obtain ⟨t, ht, -⟩ := key k le_rfl
    exact (isSome_trStopTime_iff.1 (by rw [ht]; rfl)).2
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi₁
    rw [Nat.add_sub_cancel]
    exact key j (by omega)

end CollatzPosDens
