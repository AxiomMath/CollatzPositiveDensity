/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.StoppingTrace.TrConcat
public import CollatzPosDens.StoppingTrace.TrCountConcat
public import CollatzPosDens.StoppingTrace.TrEntryPrefix
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrListSplit
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrMoment
public import CollatzPosDens.StoppingTrace.TrPathGrowthJ
public import CollatzPosDens.StoppingTrace.TrRestart
public import CollatzPosDens.StoppingTrace.TrSublist
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass

/-!
# The moment from a black origin

Fix a level `n`, put `J = ⌊n/2⌋` and fix a residue `ξ ∈ G_n`; "black" refers to `(n, ξ, ε_*)`.
For a black point `v ∈ 𝒫` and `N ∈ ℕ` with `j(v) + N > J`, the `(k+1)`-st weighted stop moment
`𝒵_{k+1}(v, β)`, averaged over `β ∈ 𝔅^N` against the block-list weight `bw^⊗`, is the `k`-th
power of the entry kernel applied to `1`:
```
∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵_{k+1}(v, β) = m_k(v).
```
The proof is by induction on `k`, for all black `v` and all admissible `N` at once. For `k = 0`
the first stop of every path from `v` is at time `0`, so `𝒵_1(v, β) = 1` and the sum is the total
mass `1` of `𝔅^N`. For the step, the second stop `q = τ_2(x)` of a live `β` is exactly the length
of the unique prefix `β_{[1,q]}` lying in the set `𝓔(v)` of entry lists; restarting the stopping
sequence at `q` factors `𝒵_{k+2}(v, β)` as
`e^{-γ_* N^*(v, β_{[1,q]}; q)} 𝒵_{k+1}(x_q, β_{[q+1,N]})`, and splitting the sum over `β` at
`q` turns the inner sum into `m_k(x_q)` by induction.

## Main results

* `CollatzPosDens.tsum_trListWeight_mul_trMoment_eq_trKernel`: the identity
  `∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵_{k+1}(v, β) = m_k(v)`.

## Implementation notes

The sum is the unconditional sum in `[0, ∞]`, the real numbers `bw^⊗(β)` and `𝒵_{k+1}(v, β)`
entering through `ENNReal.ofReal`; both are nonnegative, so nothing is truncated, and `m_k(v)` is
itself `[0, ∞]`-valued. The set `𝔅^N` is the subtype of lists of `N` blocks whose closing letters
lie in `{4, 5}`. No hypothesis `n ≥ 1` and no hypothesis that `ξ` is a unit is assumed; `n ≥ 1`
(indeed `J ≥ 1`) follows from `v ∈ 𝒫` being black.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- **The moment from a black origin.** Let `v ∈ 𝒫` be black for `(n, ξ, ε_*)`, and let `N ∈ ℕ`
with `j(v) + N > ⌊n/2⌋`. Then for every `k ∈ ℕ`,
`∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵_{k+1}(v, β) = m_k(v)`. -/
@[collatz_pos_dens "lem_tr_moment_black"]
theorem tsum_trListWeight_mul_trMoment_eq_trKernel {n : ℕ} {ξ : ResidueGroup n} {v : ℤ × ℤ}
    (hv : v ∈ bkPoints) (hvb : BkBlack n ξ (epsStar : ℝ) v) {N : ℕ}
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ v + N) (k : ℕ) :
    ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (trMoment n ξ v β.1 (k + 1)) =
      trKernel n ξ k v := by
  induction k generalizing v N with
  | zero =>
    have hJ : 0 < n / 2 := by
      have h1 := hvb.bkJ_le
      have h2 : (1 : ℤ) ≤ bkJ v := hv
      omega
    have h1 : ∀ β : List (List ℤ × ℤ), trMoment n ξ v β 1 = 1 := fun β => by
      have hτ : trStopTime n ξ (epsStar : ℝ) (trPath v β) 1 = some 0 :=
        trStopTime_one_eq_some_iff.2 ⟨hJ, by simpa [isTrHit_iff] using hvb,
          fun s hs => absurd hs (Nat.not_lt_zero s)⟩
      rw [trMoment_eq_of_trStopTime_eq_some hτ, trCount_zero, mul_zero, neg_zero, Real.exp_zero]
    simp only [zero_add, h1, ENNReal.ofReal_one, mul_one, trKernel_zero]
    exact tsum_ofReal_trListWeight_length_eq N
  | succ k ih =>
    classical
    set E := trEntryWords n ξ (epsStar : ℝ) v with hE
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → List (List ℤ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞, ∀ q u f,
        Ψ q u f = if u ∈ E then
          ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ v u q))) *
            ENNReal.ofReal (trMoment n ξ (trPath v u q) f (k + 1)) else 0 :=
      ⟨_, fun _ _ _ => rfl⟩
    obtain ⟨H, hH⟩ : ∃ H : List (List ℤ × ℤ) → ℝ≥0∞, ∀ u,
        H u = if u ∈ E then ENNReal.ofReal (trListWeight u) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length)) *
            trKernel n ξ k (trPath v u u.length) else 0 :=
      ⟨_, fun _ => rfl⟩
    have hElen : ∀ u ∈ E, u.length < N := by
      intro u hu
      have hg := trPath_bkJ_sub_bkJ_ge v u (Nat.zero_le u.length)
      simp only [min_self, Nat.zero_min, trPath_zero, CharP.cast_eq_zero, sub_zero] at hg
      have hb := (trEntryWords_bkBlack hu).bkJ_le
      omega
    have hpt : ∀ β : List (List ℤ × ℤ), β.length = N → (∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)) →
        ENNReal.ofReal (trListWeight β) * ENNReal.ofReal (trMoment n ξ v β (k + 1 + 1)) =
          ∑ q ∈ Finset.range (N + 1), ENNReal.ofReal (trListWeight β) *
            Ψ q (trSublist β 1 q) (trSublist β (q + 1) N) := by
      intro β hlen hβ
      rw [← Finset.mul_sum]
      by_cases hlive : TrLive β
      swap
      · have : trListWeight β = 0 := by
          rw [trListWeight_def]
          by_contra h
          exact hlive ((trLive_iff_prod_ne_zero β).2 h)
        simp [this]
      congr 1
      subst hlen
      have hpre := trStopTime_two_eq_some_iff_trSublist_mem_trEntryWords hv hvb β hβ hlive hN
      by_cases hex : ∃ q, 2 ≤ trNu n ξ (epsStar : ℝ) (trPath v β) ∧
          trStopTime n ξ (epsStar : ℝ) (trPath v β) 2 = some q
      · obtain ⟨q, hq⟩ := hex
        obtain ⟨hq1, hqN, hu⟩ := (hpre q).1 hq
        rw [Finset.sum_eq_single_of_mem q (Finset.mem_range.2 (by omega))]
        swap
        · intro q' hq' hne
          rw [hΨ, ite_eq_right]
          intro hu'
          have hq'N : q' ≤ β.length := by simp at hq'; omega
          have hlen' : (trSublist β 1 q').length = q' := by simp [hq'N]
          have hq'1 : 1 ≤ q' := hlen' ▸ trEntryWords_length_pos hu'
          have := (hpre q').2 ⟨hq'1, hq'N, hu'⟩
          exact hne (Option.some_inj.1 (this.2.symm.trans hq.2))
        rw [hΨ, ite_eq_left hu]
        obtain ⟨hres, -⟩ := trStopTime_trPath_restart hv hN hq.2
        have hk := hres k
        have happ : trSublist β 1 q ++ trSublist β (q + 1) β.length = β := by
          rw [trSublist_append_trSublist β le_rfl (by omega) hqN, trSublist_one_length]
        have hulen : (trSublist β 1 q).length = q := by simp [hqN]
        have hx : trPath v (trSublist β 1 q) q = trPath v β q := by
          conv_rhs => rw [← happ]
          rw [trPath_concat v _ _ hulen.ge]
        rw [hx, show k + 1 + 1 = 2 + k by omega]
        cases hτ : trStopTime n ξ (epsStar : ℝ)
            (trPath (trPath v β q) (trSublist β (q + 1) β.length)) (k + 1) with
        | none =>
          rw [hτ, Option.map_none] at hk
          rw [trMoment_eq_zero_of_trStopTime_eq_none hk,
            trMoment_eq_zero_of_trStopTime_eq_none hτ]
          simp
        | some t =>
          rw [hτ, Option.map_some] at hk
          rw [trMoment_eq_of_trStopTime_eq_some hk, trMoment_eq_of_trStopTime_eq_some hτ]
          have hc := trCount_concat ξ v (trSublist β 1 q) (trSublist β (q + 1) β.length) hulen t
          rw [happ, hx] at hc
          rw [hc, mul_add, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      · rw [Finset.sum_eq_zero]
        · rw [trMoment_eq_zero_of_not, ENNReal.ofReal_zero]
          rintro ⟨-, h2⟩
          obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1
            (isSome_trStopTime_iff (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (x := trPath v β)
              (i := 2) |>.2 ⟨by norm_num, by omega⟩)
          exact hex ⟨q, by omega, hq⟩
        · intro q hq
          rw [hΨ, ite_eq_right]
          intro hu'
          have hqN : q ≤ β.length := by simp at hq; omega
          have hlen' : (trSublist β 1 q).length = q := by simp [hqN]
          have hq1 : 1 ≤ q := hlen' ▸ trEntryWords_length_pos hu'
          exact hex ⟨q, (hpre q).2 ⟨hq1, hqN, hu'⟩⟩
    have hL : ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (trMoment n ξ v β.1 (k + 1 + 1)) =
        ∑ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) *
            Ψ q (trSublist β.1 1 q) (trSublist β.1 (q + 1) N) := by
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      exact tsum_congr fun β => hpt β.1 β.2.1 β.2.2
    have hG : ∀ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) * Ψ q (trSublist β.1 1 q) (trSublist β.1 (q + 1) N) =
        ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)},
          H u.1 := by
      intro q hq
      obtain ⟨b, rfl⟩ : ∃ b, N = q + b := ⟨N - q, by simp at hq; omega⟩
      have hsplit :=
        tsum_trListWeight_trSublist {c : List ℤ × ℤ | c.2 ∈ ({4, 5} : Set ℤ)} q b (Ψ q)
      refine hsplit.trans ?_
      refine tsum_congr fun u => ?_
      obtain ⟨u, hul, hu4⟩ := u
      subst hul
      rw [hH]
      by_cases hu : u ∈ E
      · simp only [hΨ, ite_eq_left hu]
        calc ∑' f : {f : List (List ℤ × ℤ) // f.length = b ∧ ∀ x ∈ f, x.2 ∈ ({4, 5} : Set ℤ)},
              ENNReal.ofReal (trListWeight u) * ENNReal.ofReal (trListWeight f.1) *
                (ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ v u u.length))) *
                  ENNReal.ofReal (trMoment n ξ (trPath v u u.length) f.1 (k + 1)))
            = ENNReal.ofReal (trListWeight u) *
                ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ v u u.length))) *
                ∑' f : {f : List (List ℤ × ℤ) // f.length = b ∧
                    ∀ x ∈ f, x.2 ∈ ({4, 5} : Set ℤ)},
                  ENNReal.ofReal (trListWeight f.1) *
                    ENNReal.ofReal (trMoment n ξ (trPath v u u.length) f.1 (k + 1)) := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun f => by ring
          _ = _ := by
              have hg := trPath_bkJ_sub_bkJ_ge v u (Nat.zero_le u.length)
              simp only [min_self, Nat.zero_min, trPath_zero, CharP.cast_eq_zero,
                sub_zero] at hg
              rw [ih (hv := trPath_mem_bkPoints hv u _) (hvb := trEntryWords_bkBlack hu)
                (hN := by push_cast at hN; omega), neg_mul]
      · simp only [hΨ, ite_eq_right hu]
        simp
    have hS : ∀ q, ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧
          ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)}, H u.1 =
        ∑' u : List (List ℤ × ℤ), if u.length = q then H u else 0 := by
      intro q
      rw [show (∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧
          ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)}, H u.1) = ∑' u, Set.indicator
            {u : List (List ℤ × ℤ) | u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)} H u from
        tsum_subtype {u : List (List ℤ × ℤ) | u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)} H]
      refine tsum_congr fun u => ?_
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      by_cases hq : u.length = q
      · by_cases hu : u ∈ E
        · rw [ite_eq_left ⟨hq, fun b hb => trEntryWords_closing_mem hu hb⟩, ite_eq_left hq]
        · rw [hH, ite_eq_right hu]
          simp
      · rw [ite_eq_right (fun h => hq h.1), ite_eq_right hq]
    rw [hL, Finset.sum_congr rfl hG]
    simp_rw [hS]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), trKernel_succ]
    rw [show (∑' u : E, ENNReal.ofReal (trListWeight u.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
            trKernel n ξ k (trPath v u.1 u.1.length)) = ∑' u, Set.indicator E (fun u =>
          ENNReal.ofReal (trListWeight u) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length)) *
            trKernel n ξ k (trPath v u u.length)) u from tsum_subtype E (fun u =>
          ENNReal.ofReal (trListWeight u) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length)) *
            trKernel n ξ k (trPath v u u.length))]
    refine tsum_congr fun u => ?_
    rw [Finset.sum_ite_eq]
    by_cases hu : u ∈ E
    · rw [ite_eq_left (Finset.mem_range.2 (by have := hElen u hu; omega)), Set.indicator_of_mem hu,
        hH, ite_eq_left hu]
    · rw [Set.indicator_of_notMem hu, hH, ite_eq_right hu]
      simp

end CollatzPosDens
