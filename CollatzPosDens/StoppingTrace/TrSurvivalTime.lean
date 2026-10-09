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
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.Transfer.Pinit
public import CollatzPosDens.Transfer.Schedule
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrClear
public import CollatzPosDens.StoppingTrace.TrEstar
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrTrace
public import CollatzPosDens.StoppingTrace.TrNextStop
public import CollatzPosDens.StoppingTrace.TrRecipeIterMono
public import CollatzPosDens.StoppingTrace.TrRecipeMono
public import CollatzPosDens.StoppingTrace.TrSurvivalFirstHit

/-!
# Survival: the stops come on schedule

Let `J = ⌊n/2⌋`, let `ξ ∈ G_n` be a unit, and let black and white refer to `(n, ξ, ε_*)`. Let
`e ∈ 𝒫` and `m ∈ ℕ` with `j(e) + m = J`, assume `P_* ≤ J`, and let `a = ((r, ℓ), β) ∈ 𝒜_n` with
`β` live and `a ∈ Low^e \ (Bad^e_m ∪ E^{*,e} ∪ Clr)`. Write `y = (y^e_p(a))_{p ∈ ℕ}`. Then for
every `1 ≤ i ≤ r_* + 1` the stopping sequence of `y` has at least `i` terms, and its `i`-th term
satisfies `τ_i(y) ≤ p_{i-1}`.

The proof is by induction on `i`. The first hit `c ≤ T_* + 1 = 102 ≤ 1024 = p_0` below `J`
bounds `τ_1(y)`. If `q = τ_i(y) ≤ p_{i-1}` with `i ≤ r_*`, then `y_q` is black and
`𝔤(q) ≤ 𝔤(p_{i-1}) = p_i ≤ p_{r_*} = P_* - 1`, so the next stop lemma gives a hit `c` of `y`
after `q` with `q < c ≤ 𝔤(q)` and `c < J`; hence `τ_{i+1}(y)` is defined and at most
`c ≤ p_i`.

## Main results

* `CollatzPosDens.le_trNu_and_trStopTime_le_schedule`: for `1 ≤ i ≤ r_* + 1`, the stopping
  sequence of `y` has at least `i` terms and `τ_i(y) ≤ p_{i-1}`.

## Implementation notes

The `i`-th term of the stopping sequence is `trStopTime n ξ ε_* y i : Option ℕ`; the conclusion
records that `i ≤ ν(y)` and that this term is `some t` with `t ≤ p_{i-1}`. The membership
`a ∈ 𝒜_n` is part of `a ∈ Low^e`, and liveness of `β` is `TrLive a.2`. The hypothesis `n ≥ 1`
is not used and is dropped, which generalizes the source.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `J = ⌊n/2⌋`, `ξ ∈ G_n` a unit, `e` an entry point and `m ∈ ℕ` with `j(e) + m = J`,
`P_* ≤ J`, and `a = ((r, ℓ), β)` with `β` live and `a ∈ Low^e \ (Bad^e_m ∪ E^{*,e} ∪ Clr)`. Then
for every `1 ≤ i ≤ r_* + 1`, the stopping sequence of `y = (y^e_p(a))_p` (for `(n, ξ, ε_*)`) has
at least `i` terms, and its `i`-th term `τ_i(y)` is at most `p_{i-1}`. -/
@[collatz_pos_dens "lem_tr_survival_time"]
theorem le_trNu_and_trStopTime_le_schedule {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {e : ℤ × ℤ} (he : e ∈ bkPoints) {m : ℕ}
    (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ))
    (hP : pStar ≤ n / 2) {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hlive : TrLive a.2)
    (hlow : a ∈ trLow n ξ e) (hbad : a ∉ trBad n e m) (hE : a ∉ trEStar n ξ e)
    (hclr : a ∉ trClear n) {i : ℕ} (hi₁ : 1 ≤ i) (hiR : i ≤ rStar + 1) :
    i ≤ trNu n ξ (epsStar : ℝ) (trFreshPath e a) ∧
      ∃ t, trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) i = some t ∧
        t ≤ schedule (i - 1) := by
  set y := trFreshPath e a with hy
  suffices h : ∃ t, trStopTime n ξ (epsStar : ℝ) y i = some t ∧ t ≤ schedule (i - 1) by
    obtain ⟨t, ht, hle⟩ := h
    exact ⟨(isSome_trStopTime_iff.1 (by rw [ht]; rfl)).2, t, ht, hle⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hi₁
  induction k with
  | zero =>
    obtain ⟨c, -, hcT, hcJ, hc⟩ :=
      exists_bkBlack_trFreshPath_of_mem_trLow_diff_trBad hm hP ⟨hlow, hbad⟩
    have hc0 : c ≤ schedule 0 := by
      rw [schedule_zero, pInit_def]; rw [tStar_def] at hcT; omega
    rcases ht : trStopTime n ξ (epsStar : ℝ) y 1 with _ | t
    · exact absurd hc ((trStopTime_one_eq_none_iff.1 ht) c hcJ)
    · refine ⟨t, rfl, ?_⟩
      have hmin := (trStopTime_one_eq_some_iff.1 ht).2.2
      exact (not_lt.1 fun hlt => hmin c hlt hc).trans hc0
  | succ k ih =>
    obtain ⟨q, hq, hqle⟩ := ih (by omega) (by omega)
    rw [Nat.add_sub_cancel] at hqle
    rw [show k + 1 + 1 - 1 = k + 1 by omega]
    have hqb : BkBlack n ξ (epsStar : ℝ) (y q) := isTrHit_of_trStopTime_eq_some hq
    have hgq : recipeMap q ≤ schedule (k + 1) := by
      rw [schedule_succ]; exact recipeMap_le_recipeMap hqle
    have hgP : recipeMap q ≤ pStar - 1 := by
      have := schedule_le_schedule (show k + 1 ≤ rStar by omega)
      rw [pStar_def]; omega
    obtain ⟨c, hqc, hcg, hcJ, hcb, hctop⟩ :=
      exists_bkBlack_trFreshPath_bkColTop_lt hξ he hm hP hlive hlow hbad hE hclr hqb hgP
    have hhit : IsTrHitAfter n ξ (epsStar : ℝ) y q c := ⟨hcb, hctop⟩
    rcases ht : trStopTime n ξ (epsStar : ℝ) y (k + 2) with _ | t
    · exact absurd hhit ((trStopTime_succ_succ_eq_none_iff hq).1 ht c hcJ hqc)
    · refine ⟨t, rfl, ?_⟩
      obtain ⟨q', hq', -, -, hmin⟩ := trStopTime_succ_succ_eq_some_iff.1 ht
      rw [hq, Option.some_inj] at hq'
      subst hq'
      exact ((not_lt.1 fun hlt => hmin c hlt ⟨hqc, hhit⟩).trans hcg).trans hgq

end CollatzPosDens
