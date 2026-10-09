/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Rho
public import CollatzPosDens.StoppingTrace.TrConcat
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrCountConcat
public import CollatzPosDens.StoppingTrace.TrFirstStopPrefix
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrKernelPowers
public import CollatzPosDens.StoppingTrace.TrListSplit
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrMoment
public import CollatzPosDens.StoppingTrace.TrMomentBlack
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrPathGrowthJ
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass
public import CollatzPosDens.StoppingTrace.TrRestart
public import CollatzPosDens.StoppingTrace.TrReward
public import CollatzPosDens.StoppingTrace.TrSublist

/-!
# Tao's Lemma 7.9 at the explicit parameters

Fix a level `n`, put `J = ⌊n/2⌋` and fix a unit `ξ ∈ G_n`; "black" refers to `(n, ξ, ε_*)`.
For a starting point `o ∈ 𝒫`, a length `N ∈ ℕ` with `j(o) + N > J` and `R ≥ 1`, the `R`-th
weighted stop moment, averaged over `β ∈ 𝔅^N` against the block-list weight `bw^⊗`, is bounded
by the two-passage rate:
```
∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵_R(o, β) ≤ ϱ_*^{⌊(R-1)/2⌋} (1 - d_*)^{R-1-2⌊(R-1)/2⌋}.
```
The first stop `q = τ_1(x)` of a live `β` is the length of the unique prefix `β_{[1,q]}` lying
in the set `𝒰(o)` of first-stop lists. Restarting the stopping sequence at `q` factors
`𝒵_R(o, β)` as `e^{-γ_* N^*(o, β_{[1,q]}; q)} 𝒵_R(x_q, β_{[q+1,N]})`, the point `x_q` being black.
Splitting the sum over `β` at `q`, the inner sum is the moment from a black origin, i.e. the
entry kernel power `m_{R-1}(x_q)`, which is bounded by the right side; the factor
`e^{-γ_* N^*}` is at most `1`, and `𝒰(o)` is prefix-free with lists of length at most `J`, so
its total weight is at most `1`.

## Main results

* `CollatzPosDens.tsum_trListWeight_mul_trMoment_le`: the bound above.

## Implementation notes

The sum is the unconditional sum in `[0, ∞]`, the real numbers `bw^⊗(β)` and `𝒵_R(o, β)`
entering through `ENNReal.ofReal`; both are nonnegative, so nothing is truncated. The set `𝔅^N`
is the subtype of lists of `N` blocks whose closing letters lie in `{4, 5}`. The standing
hypothesis `n ≥ 1` is not used and is dropped.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- **Tao's Lemma 7.9.** Let `ξ ∈ G_n` be a unit, `o ∈ 𝒫`, `N ∈ ℕ` with `j(o) + N > ⌊n/2⌋`,
and `R ≥ 1`. Then
`∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵_R(o, β) ≤ ϱ_*^{⌊(R-1)/2⌋} (1 - d_*)^{R-1-2⌊(R-1)/2⌋}`. -/
@[collatz_pos_dens "lem_tr_lemma79"]
theorem tsum_trListWeight_mul_trMoment_le {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {o : ℤ × ℤ} (ho : o ∈ bkPoints) {N : ℕ} (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + N) {R : ℕ}
    (hR : 1 ≤ R) :
    ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (trMoment n ξ o β.1 R) ≤
      ENNReal.ofReal ((rhoStar : ℝ) ^ ((R - 1) / 2) *
        (1 - (dStar : ℝ)) ^ (R - 1 - 2 * ((R - 1) / 2))) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, R = k + 1 := ⟨R - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set C := ENNReal.ofReal ((rhoStar : ℝ) ^ (k / 2) * (1 - (dStar : ℝ)) ^ (k - 2 * (k / 2)))
    with hC
  set U := trFirstStopSet n ξ (epsStar : ℝ) o with hU
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → List (List ℤ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞, ∀ q u f,
      Ψ q u f = if u ∈ U then
        ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o u q))) *
          ENNReal.ofReal (trMoment n ξ (trPath o u q) f (k + 1)) else 0 :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : List (List ℤ × ℤ) → ℝ≥0∞, ∀ u,
      G u = if u ∈ U then ENNReal.ofReal (trListWeight u) * C else 0 :=
    ⟨_, fun _ => rfl⟩
  -- every first-stop list ends at a black point, so has length at most `J`
  have hUlen : ∀ u ∈ U, u.length ≤ n / 2 := by
    intro u hu
    have hg := trPath_bkJ_sub_bkJ_ge o u (Nat.zero_le u.length)
    simp only [min_self, Nat.zero_min, trPath_zero, CharP.cast_eq_zero, sub_zero] at hg
    have hb := (trFirstStopSet_bkBlack hu).bkJ_le
    have ho1 : (1 : ℤ) ≤ bkJ o := ho
    omega
  -- the pointwise decomposition of `𝒵_{k+1}(o, β)` at the first stop
  have hpt : ∀ β : List (List ℤ × ℤ), β.length = N → (∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)) →
      ENNReal.ofReal (trListWeight β) * ENNReal.ofReal (trMoment n ξ o β (k + 1)) =
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
    have hpre := trStopTime_one_eq_some_iff_trSublist_mem_trFirstStopSet (n := n) (ξ := ξ)
      (ε := (epsStar : ℝ)) ho β hβ hlive hN
    by_cases hex : ∃ q, 1 ≤ trNu n ξ (epsStar : ℝ) (trPath o β) ∧
        trStopTime n ξ (epsStar : ℝ) (trPath o β) 1 = some q
    · obtain ⟨q, hq⟩ := hex
      obtain ⟨hqN, hu⟩ := (hpre q).1 hq
      rw [Finset.sum_eq_single_of_mem q (Finset.mem_range.2 (by omega))]
      swap
      · intro q' hq' hne
        rw [hΨ, ite_eq_right]
        intro hu'
        have hq'N : q' ≤ β.length := by simp at hq'; omega
        have := (hpre q').2 ⟨hq'N, hu'⟩
        exact hne (Option.some_inj.1 (this.2.symm.trans hq.2))
      rw [hΨ, ite_eq_left hu]
      obtain ⟨hres, -⟩ := trStopTime_trPath_restart ho hN hq.2
      have hk := hres k
      rw [Nat.add_comm 1 k] at hk
      have happ : trSublist β 1 q ++ trSublist β (q + 1) β.length = β := by
        rw [trSublist_append_trSublist β le_rfl (by omega) hqN, trSublist_one_length]
      have hulen : (trSublist β 1 q).length = q := by simp [hqN]
      have hx : trPath o (trSublist β 1 q) q = trPath o β q := by
        conv_rhs => rw [← happ]
        rw [trPath_concat o _ _ hulen.ge]
      rw [hx]
      cases hτ : trStopTime n ξ (epsStar : ℝ)
          (trPath (trPath o β q) (trSublist β (q + 1) β.length)) (k + 1) with
      | none =>
        rw [hτ, Option.map_none] at hk
        rw [trMoment_eq_zero_of_trStopTime_eq_none hk,
          trMoment_eq_zero_of_trStopTime_eq_none hτ]
        simp
      | some t =>
        rw [hτ, Option.map_some] at hk
        rw [trMoment_eq_of_trStopTime_eq_some hk, trMoment_eq_of_trStopTime_eq_some hτ]
        have hc := trCount_concat ξ o (trSublist β 1 q) (trSublist β (q + 1) β.length) hulen t
        rw [happ, hx] at hc
        rw [hc, mul_add, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    · rw [Finset.sum_eq_zero]
      · rw [trMoment_eq_zero_of_not, ENNReal.ofReal_zero]
        rintro ⟨-, h2⟩
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1
          (isSome_trStopTime_iff (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (x := trPath o β)
            (i := 1) |>.2 ⟨le_rfl, by omega⟩)
        exact hex ⟨q, by omega, hq⟩
      · intro q hq
        rw [hΨ, ite_eq_right]
        intro hu'
        have hqN : q ≤ β.length := by simp at hq; omega
        exact hex ⟨q, (hpre q).2 ⟨hqN, hu'⟩⟩
  -- sum the decomposition over `β`
  have hL : ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
        ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) * ENNReal.ofReal (trMoment n ξ o β.1 (k + 1)) =
      ∑ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
        ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) *
          Ψ q (trSublist β.1 1 q) (trSublist β.1 (q + 1) N) := by
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    exact tsum_congr fun β => hpt β.1 β.2.1 β.2.2
  -- split each sum at `q` and bound the inner sum by the moment from a black origin
  have hB : ∀ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
        ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) * Ψ q (trSublist β.1 1 q) (trSublist β.1 (q + 1) N) ≤
      ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)},
        G u.1 := by
    intro q hq
    obtain ⟨b, rfl⟩ : ∃ b, N = q + b := ⟨N - q, by simp at hq; omega⟩
    refine le_of_eq_of_le
      (tsum_trListWeight_trSublist {c : List ℤ × ℤ | c.2 ∈ ({4, 5} : Set ℤ)} q b (Ψ q)) ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    obtain ⟨u, hul, hu4⟩ := u
    subst hul
    rw [hG]
    by_cases hu : u ∈ U
    · simp only [hΨ, ite_eq_left hu]
      have hg := trPath_bkJ_sub_bkJ_ge o u (Nat.zero_le u.length)
      simp only [min_self, Nat.zero_min, trPath_zero, CharP.cast_eq_zero, sub_zero] at hg
      have hblack := trFirstStopSet_bkBlack hu
      have hxP := trPath_mem_bkPoints ho u u.length
      calc ∑' f : {f : List (List ℤ × ℤ) // f.length = b ∧ ∀ x ∈ f, x.2 ∈ ({4, 5} : Set ℤ)},
            ENNReal.ofReal (trListWeight u) * ENNReal.ofReal (trListWeight f.1) *
              (ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o u u.length))) *
                ENNReal.ofReal (trMoment n ξ (trPath o u u.length) f.1 (k + 1)))
          = ENNReal.ofReal (trListWeight u) *
              ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o u u.length))) *
              ∑' f : {f : List (List ℤ × ℤ) // f.length = b ∧
                  ∀ x ∈ f, x.2 ∈ ({4, 5} : Set ℤ)},
                ENNReal.ofReal (trListWeight f.1) *
                  ENNReal.ofReal (trMoment n ξ (trPath o u u.length) f.1 (k + 1)) := by
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun f => by ring
        _ = ENNReal.ofReal (trListWeight u) *
              ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o u u.length))) *
              trKernel n ξ k (trPath o u u.length) := by
            rw [tsum_trListWeight_mul_trMoment_eq_trKernel hxP hblack
              (by push_cast at hN; omega)]
        _ ≤ ENNReal.ofReal (trListWeight u) * 1 * C := by
            gcongr
            · refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 ?_))
              exact mul_nonneg (by exact_mod_cast gammaStar_pos.le) (trCount_nonneg _ _ _)
            · exact trKernel_le_rhoStar_pow hξ k hxP hblack
        _ = ENNReal.ofReal (trListWeight u) * C := by rw [mul_one]
    · simp only [hΨ, ite_eq_right hu]
      simp
  -- reassemble the sum over the first-stop lists
  have hS : ∀ q, ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧
        ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)}, G u.1 =
      ∑' u : List (List ℤ × ℤ), if u.length = q then G u else 0 := by
    intro q
    rw [show (∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧
        ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)}, G u.1) = ∑' u, Set.indicator
          {u : List (List ℤ × ℤ) | u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)} G u from
      tsum_subtype {u : List (List ℤ × ℤ) | u.length = q ∧ ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)} G]
    refine tsum_congr fun u => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases hq : u.length = q
    · by_cases hu : u ∈ U
      · rw [ite_eq_left ⟨hq, fun b hb => trFirstStopSet_closing_mem hu hb⟩, ite_eq_left hq]
      · rw [hG, ite_eq_right hu]
        simp
    · rw [ite_eq_right (fun h => hq h.1), ite_eq_right hq]
  -- the total weight of the first-stop lists is at most `1`
  have hmass : ∑' u : U, ENNReal.ofReal (trListWeight u.1) ≤ 1 :=
    tsum_trListWeight_le_one_of_prefixFree (n / 2) U
      (fun u hu b hb => trFirstStopSet_closing_mem hu hb) hUlen
      isPrefixFree_trFirstStopSet
  calc _ = _ := hL
    _ ≤ ∑ q ∈ Finset.range (N + 1), ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧
          ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)}, G u.1 := Finset.sum_le_sum hB
    _ = ∑' u : List (List ℤ × ℤ), ∑ q ∈ Finset.range (N + 1),
          if u.length = q then G u else 0 := by
        simp_rw [hS]
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑' u : List (List ℤ × ℤ), G u := by
        refine ENNReal.tsum_le_tsum fun u => ?_
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp
    _ = ∑' u : U, ENNReal.ofReal (trListWeight u.1) * C := by
        rw [tsum_subtype U (fun u => ENNReal.ofReal (trListWeight u) * C)]
        refine tsum_congr fun u => ?_
        rw [hG, Set.indicator_apply]
    _ = (∑' u : U, ENNReal.ofReal (trListWeight u.1)) * C := ENNReal.tsum_mul_right
    _ ≤ 1 * C := by gcongr
    _ = C := one_mul C

end CollatzPosDens
