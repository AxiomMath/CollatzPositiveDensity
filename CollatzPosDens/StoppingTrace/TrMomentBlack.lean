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

/-- From a black origin the first stop is at time `0`, so `𝒵_1(v, β) = 1`. -/
theorem trMoment_one_of_bkBlack {n : ℕ} {ξ : ResidueGroup n} {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hvb : BkBlack n ξ (epsStar : ℝ) v) (β : List (List ℤ × ℤ)) : trMoment n ξ v β 1 = 1 := by
  have hJ : 0 < n / 2 := by
    have h1 := hvb.bkJ_le
    have h2 : (1 : ℤ) ≤ bkJ v := hv
    omega
  have hτ : trStopTime n ξ (epsStar : ℝ) (trPath v β) 1 = some 0 :=
    trStopTime_one_eq_some_iff.2 ⟨hJ, by simpa [isTrHit_iff] using hvb,
      fun s hs => absurd hs (Nat.not_lt_zero s)⟩
  rw [trMoment_eq_of_trStopTime_eq_some hτ, trCount_zero, mul_zero, neg_zero, Real.exp_zero]

/-- Following a list of `u.length` blocks raises the `j`-coordinate by at least `u.length`. -/
theorem bkJ_add_length_le_bkJ_trPath (v : ℤ × ℤ) (u : List (List ℤ × ℤ)) :
    bkJ v + u.length ≤ bkJ (trPath v u u.length) := by
  have hg := trPath_bkJ_sub_bkJ_ge v u (Nat.zero_le u.length)
  simp only [min_self, Nat.zero_min, trPath_zero, CharP.cast_eq_zero, sub_zero] at hg
  omega

/-- A list that is not live has block-list weight zero. -/
theorem trListWeight_eq_zero_of_not_trLive {β : List (List ℤ × ℤ)} (h : ¬TrLive β) :
    trListWeight β = 0 := by
  rw [trListWeight_def]
  by_contra h'
  exact h ((trLive_iff_prod_ne_zero β).2 h')

/-- Every entry list from a black origin `v` with `j(v) + N > ⌊n/2⌋` is shorter than `N`. -/
theorem length_lt_of_mem_trEntryWords {n : ℕ} {ξ : ResidueGroup n} {v : ℤ × ℤ} {N : ℕ}
    {u : List (List ℤ × ℤ)} (hN : ((n / 2 : ℕ) : ℤ) < bkJ v + N)
    (hu : u ∈ trEntryWords n ξ (epsStar : ℝ) v) : u.length < N := by
  have := bkJ_add_length_le_bkJ_trPath v u
  have := (trEntryWords_bkBlack hu).bkJ_le
  omega

/-- The `(k+2)`-nd weighted stop moment of a live list from a black origin, decomposed at the
second stop over the entry lists `β_{[1,q]} ∈ 𝓔(v)`. -/
theorem ofReal_trMoment_add_two_eq_sum {n : ℕ} {ξ : ResidueGroup n} {v : ℤ × ℤ}
    (hv : v ∈ bkPoints) (hvb : BkBlack n ξ (epsStar : ℝ) v) (β : List (List ℤ × ℤ))
    (hβ : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)) (hlive : TrLive β)
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ v + β.length) (k : ℕ) :
    ENNReal.ofReal (trMoment n ξ v β (k + 1 + 1)) =
      ∑ q ∈ Finset.range (β.length + 1), (trEntryWords n ξ (epsStar : ℝ) v).indicator
        (fun u => ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ v u q))) *
          ENNReal.ofReal (trMoment n ξ (trPath v u q) (trSublist β (q + 1) β.length) (k + 1)))
        (trSublist β 1 q) := by
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
      rw [trMoment_eq_zero_of_trStopTime_eq_none hk, trMoment_eq_zero_of_trStopTime_eq_none hτ]
      simp
    | some t =>
      rw [hτ, Option.map_some] at hk
      rw [trMoment_eq_of_trStopTime_eq_some hk, trMoment_eq_of_trStopTime_eq_some hτ]
      have hc := trCount_concat ξ v (trSublist β 1 q) (trSublist β (q + 1) β.length) hulen t
      rw [happ, hx] at hc
      rw [hc, mul_add, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  · rw [Finset.sum_eq_zero fun q hq =>
      Set.indicator_of_notMem (fun hu' => hex ⟨q, hstop q hq hu'⟩) _,
      trMoment_eq_zero_of_not, ENNReal.ofReal_zero]
    rintro ⟨-, h2⟩
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1
      (isSome_trStopTime_iff (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (x := trPath v β)
        (i := 2) |>.2 ⟨by norm_num, by omega⟩)
    exact hex ⟨q, by omega, hq⟩

/-- Summing an indicator of `E` over the lists of each length `q ≤ N` recovers the sum over `E`,
when every list of `E` has length `< N` and closing letters in `{4, 5}`. -/
theorem sum_range_tsum_indicator_eq_tsum {N : ℕ} (E : Set (List (List ℤ × ℤ)))
    (F : List (List ℤ × ℤ) → ℝ≥0∞)
    (hE : ∀ u ∈ E, u.length < N ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)) :
    ∑ q ∈ Finset.range (N + 1),
        ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)},
          E.indicator F u.1 =
      ∑' u : E, F u.1 := by
  have hS : ∀ q, ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧
      ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)}, E.indicator F u.1 =
        ∑' u, if u.length = q then E.indicator F u else 0 := fun q =>
    (tsum_subtype {u : List (List ℤ × ℤ) | u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)}
      (E.indicator F)).trans <| tsum_congr fun u => by
        by_cases hu : u ∈ E
        · by_cases hq : u.length = q
          · rw [Set.indicator_of_mem (show u ∈ {u : List (List ℤ × ℤ) | u.length = q ∧
              ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)} from ⟨hq, (hE u hu).2⟩), ite_eq_left hq]
          · rw [Set.indicator_of_notMem (fun h => hq h.1), ite_eq_right hq]
        · simp [hu]
  rw [Finset.sum_congr rfl fun q _ => hS q,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine (tsum_congr fun u => ?_).trans (tsum_subtype E F).symm
  rw [Finset.sum_ite_eq]
  by_cases hu : u ∈ E
  · rw [ite_eq_left (Finset.mem_range.2 (by have := (hE u hu).1; omega))]
  · simp [hu]

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
    simp only [zero_add, trMoment_one_of_bkBlack hv hvb, ENNReal.ofReal_one, mul_one,
      trKernel_zero]
    exact tsum_ofReal_trListWeight_length_eq N
  | succ k ih =>
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → List (List ℤ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞, ∀ q u f,
        Ψ q u f = (trEntryWords n ξ (epsStar : ℝ) v).indicator (fun u =>
          ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ v u q))) *
            ENNReal.ofReal (trMoment n ξ (trPath v u q) f (k + 1))) u :=
      ⟨_, fun _ _ _ => rfl⟩
    have hL : ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (trMoment n ξ v β.1 (k + 1 + 1)) =
        ∑ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) *
            Ψ q (trSublist β.1 1 q) (trSublist β.1 (q + 1) N) := by
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr fun β => ?_
      obtain ⟨hlen, hβ⟩ := β.2
      rw [← Finset.mul_sum]
      by_cases hlive : TrLive β.1
      · have h := ofReal_trMoment_add_two_eq_sum hv hvb β.1 hβ hlive (by rw [hlen]; exact hN) k
        rw [hlen] at h
        simp only [h, hΨ]
      · simp [trListWeight_eq_zero_of_not_trLive hlive]
    have hG : ∀ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) * Ψ q (trSublist β.1 1 q) (trSublist β.1 (q + 1) N) =
        ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)},
          (trEntryWords n ξ (epsStar : ℝ) v).indicator (fun u =>
            ENNReal.ofReal (trListWeight u) *
              ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length)) *
                trKernel n ξ k (trPath v u u.length)) u.1 := by
      intro q hq
      obtain ⟨b, rfl⟩ : ∃ b, N = q + b := ⟨N - q, by have := Finset.mem_range.1 hq; omega⟩
      refine (tsum_trListWeight_trSublist {c : List ℤ × ℤ | c.2 ∈ ({4, 5} : Set ℤ)} q b
        (Ψ q)).trans (tsum_congr fun u => ?_)
      obtain ⟨u, rfl, -⟩ := u
      by_cases hu : u ∈ trEntryWords n ξ (epsStar : ℝ) v
      · simp only [hΨ, Set.indicator_of_mem hu]
        have := bkJ_add_length_le_bkJ_trPath v u
        rw [← ih (v := trPath v u u.length) (N := b) (trPath_mem_bkPoints hv u _)
          (trEntryWords_bkBlack hu) (by push_cast at hN; omega), ← ENNReal.tsum_mul_left]
        exact tsum_congr fun f => by rw [neg_mul]; ring
      · simp only [hΨ, Set.indicator_of_notMem hu, mul_zero, tsum_zero]
    rw [hL, Finset.sum_congr rfl hG, sum_range_tsum_indicator_eq_tsum (N := N) _ _
      fun u hu => ⟨length_lt_of_mem_trEntryWords hN hu, fun b hb => trEntryWords_closing_mem hu hb⟩,
      trKernel_succ]

end CollatzPosDens
