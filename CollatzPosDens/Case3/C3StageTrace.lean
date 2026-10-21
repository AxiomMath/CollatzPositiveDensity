/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageMassBound
public import CollatzPosDens.Case3.C3StageMomentBlack
public import CollatzPosDens.StoppingTrace.TrLemma79

/-!
# Discounted stages from any starting point

Fix a level `n`, put `J = ⌊n/2⌋` and fix a unit `ξ ∈ G_n`; "black" refers to `(n, ξ, ε_*)`. For
a starting point `o ∈ 𝒫`, `N ∈ ℕ` with `j(o) + N > J`, and integers `d ≥ 1` and `k ≥ 0`,
```
∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵^{4096,d}_{k,d}(o, β) ≤ max(b_*, (77/100)^d)^k,
```
where `𝒵^{G,d}_{k,t}` is the discount at the end of the stages and `b_* = 333407/10⁶`.

The first stop `q = τ_1(x)` of a live `β` is the length of the unique prefix `u = β_{[1,q]}`
lying in the set `𝒰(o)` of first-stop lists. Restarting the stopping sequence at `q`
(`CollatzPosDens.trStopTime_trPath_restart`, `CollatzPosDens.trStageEnd_add_of_shift` with
`c = 0`) leaves the stage end index unchanged and factors
`𝒵(o, β) = e^{-γ_* N^*(o, u; q)} 𝒵(x_q(o, u), β_{[q+1,N]})`, the point `x_q(o, u)` being black.
Splitting the sum over `β` at `q`, the inner sum is the stopped-stage mass
`𝓜^{4096,d}_{k,d}(x_q(o, u))`
(`CollatzPosDens.tsum_trListWeight_mul_trStageMoment_eq_trStageMass`), at most
`max(b_*, (77/100)^d)^k` (`CollatzPosDens.trStageMass_le` with `t = d`); the factor `e^{-γ_* N^*}`
is at most `1`, and `𝒰(o)` is prefix-free with lists of length at most `J`, so its total weight is
at most `1`.

## Main results

* `CollatzPosDens.ofReal_trStageMoment_eq_of_trStopTime_one_eq_some`: the factorization of
  `𝒵^{G,d}_{k,t}(o, β)` at the first stop.
* `CollatzPosDens.tsum_trListWeight_mul_trStageMoment_le`: the bound above.

## Implementation notes

The sum is the unconditional sum in `[0, ∞]`, the real numbers `bw^⊗(β)` and `𝒵(o, β)` entering
through `ENNReal.ofReal`; both are nonnegative, so nothing is truncated. The set `𝔅^N` is the
subtype of lists of `N` blocks whose closing letters lie in `{4, 5}`. The standing hypothesis
`n ≥ 1` is not used and is dropped.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n} {G : ℤ} {d : ℕ}

/-- If the first stop of `β` from `o` is `q`, restarting at `q` factors the discount at the end of
the stages: `𝒵^{G,d}_{k,t}(o, β) = e^{-γ_* N^*(o, β_{[1,q]}; q)}
𝒵^{G,d}_{k,t}(x_q(o, β_{[1,q]}), β_{[q+1,N]})`. -/
theorem ofReal_trStageMoment_eq_of_trStopTime_one_eq_some {o : ℤ × ℤ} (ho : o ∈ bkPoints)
    {β : List (List ℤ × ℤ)} (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + β.length) {q : ℕ}
    (hq : trStopTime n ξ (epsStar : ℝ) (trPath o β) 1 = some q) (hqN : q ≤ β.length)
    (k t : ℕ) :
    ENNReal.ofReal (trStageMoment n ξ G d k t o β) =
      ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o (trSublist β 1 q) q))) *
        ENNReal.ofReal (trStageMoment n ξ G d k t (trPath o (trSublist β 1 q) q)
          (trSublist β (q + 1) β.length)) := by
  obtain ⟨hres, hν⟩ := trStopTime_trPath_restart ho hN hq
  have happ : trSublist β 1 q ++ trSublist β (q + 1) β.length = β := by
    rw [trSublist_append_trSublist β le_rfl (by omega) hqN, trSublist_one_length]
  have hulen : (trSublist β 1 q).length = q := by simp [hqN]
  have hx : trPath o (trSublist β 1 q) q = trPath o β q := by
    conv_rhs => rw [← happ]
    rw [trPath_concat o _ _ hulen.ge]
  rw [hx]
  set x' := trPath (trPath o β q) (trSublist β (q + 1) β.length)
  have hshift : ∀ w, trPath o β (q + w) = x' w := fun w => by
    conv_lhs => rw [← happ]
    rw [trPath_append_add o _ _ hulen w, hx]
  have hν' : trNu n ξ (epsStar : ℝ) (trPath o β) = 0 + trNu n ξ (epsStar : ℝ) x' := hν
  have hτ : ∀ i, 1 ≤ i → i ≤ trNu n ξ (epsStar : ℝ) x' →
      trStopTime n ξ (epsStar : ℝ) (trPath o β) (0 + i) =
        (trStopTime n ξ (epsStar : ℝ) x' i).map (q + ·) := fun i hi _ => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    rw [show 0 + (m + 1) = 1 + m by omega]
    exact hres m
  have hse := trStageEnd_add_of_shift (G := G) (d := d) hshift hν' hτ k t 1 le_rfl
  rw [Nat.zero_add, Nat.cast_zero, zero_add] at hse
  have h1 := le_trStageEnd (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (G := G) (d := d) (x := x')
    k t 1
  cases hi : trStageEnd n ξ (epsStar : ℝ) G d x' k t 1 using ENat.recTopCoe with
  | top =>
    rw [hi] at hse
    rw [trStageMoment_eq_zero_of_eq_top hse, trStageMoment_eq_zero_of_eq_top hi]
    simp
  | coe i =>
    rw [hi] at hse h1
    have hi1 : 1 ≤ i := by exact_mod_cast h1
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi1
    have hτm := hres m
    rw [show 1 + m = m + 1 by omega] at hτm
    cases hs : trStopTime n ξ (epsStar : ℝ) x' (m + 1) with
    | none =>
      rw [hs, Option.map_none] at hτm
      rw [trStageMoment_eq_zero_of_trStopTime_eq_none hse hτm,
        trStageMoment_eq_zero_of_trStopTime_eq_none hi hs]
      simp
    | some s =>
      rw [hs, Option.map_some] at hτm
      rw [trStageMoment_eq_of_trStopTime_eq_some hse hτm,
        trStageMoment_eq_of_trStopTime_eq_some hi hs]
      have hc := trCount_concat ξ o (trSublist β 1 q) (trSublist β (q + 1) β.length) hulen s
      rw [happ, hx] at hc
      rw [hc, mul_add, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

open Classical in
/-- For a live `β`, the discount `𝒵^{G,d}_{k,t}(o, β)` decomposes over the first stop `q`, the
prefix `β_{[1,q]}` being the unique one lying in `𝒰(o)`. -/
theorem ofReal_trStageMoment_eq_sum_of_trLive {o : ℤ × ℤ} (ho : o ∈ bkPoints)
    {β : List (List ℤ × ℤ)} (hβ : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)) (hlive : TrLive β)
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + β.length) (k t : ℕ) :
    ENNReal.ofReal (trStageMoment n ξ G d k t o β) =
      ∑ q ∈ Finset.range (β.length + 1), if trSublist β 1 q ∈ trFirstStopSet n ξ (epsStar : ℝ) o
        then ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o (trSublist β 1 q) q))) *
          ENNReal.ofReal (trStageMoment n ξ G d k t (trPath o (trSublist β 1 q) q)
            (trSublist β (q + 1) β.length))
        else 0 := by
  have hpre := trStopTime_one_eq_some_iff_trSublist_mem_trFirstStopSet (n := n) (ξ := ξ)
    (ε := (epsStar : ℝ)) ho β hβ hlive hN
  by_cases hex : ∃ q, 1 ≤ trNu n ξ (epsStar : ℝ) (trPath o β) ∧
      trStopTime n ξ (epsStar : ℝ) (trPath o β) 1 = some q
  · obtain ⟨q, hq⟩ := hex
    obtain ⟨hqN, hu⟩ := (hpre q).1 hq
    rw [Finset.sum_eq_single_of_mem q (Finset.mem_range.2 (by omega))]
    swap
    · intro q' hq' hne
      rw [ite_eq_right]
      intro hu'
      have hq'N : q' ≤ β.length := by simp at hq'; omega
      have := (hpre q').2 ⟨hq'N, hu'⟩
      exact hne (Option.some_inj.1 (this.2.symm.trans hq.2))
    rw [ite_eq_left hu]
    exact ofReal_trStageMoment_eq_of_trStopTime_one_eq_some ho hN hq.2 hqN k t
  · rw [Finset.sum_eq_zero]
    · have hν : trNu n ξ (epsStar : ℝ) (trPath o β) = 0 := by
        by_contra h0
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1
          (isSome_trStopTime_iff (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (x := trPath o β)
            (i := 1) |>.2 ⟨le_rfl, by omega⟩)
        exact hex ⟨q, by omega, hq⟩
      have h1 := le_trStageEnd (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) (G := G) (d := d)
        (x := trPath o β) k t 1
      rw [trStageMoment_eq_zero_of_trNu_lt (lt_of_lt_of_le (by rw [hν]; exact_mod_cast
        Nat.zero_lt_one) h1), ENNReal.ofReal_zero]
    · intro q hq
      rw [ite_eq_right]
      intro hu'
      have hqN : q ≤ β.length := by simp at hq; omega
      exact hex ⟨q, (hpre q).2 ⟨hqN, hu'⟩⟩

open Classical in
/-- The pointwise first-stop decomposition of `bw^⊗(β) 𝒵^{G,d}_{k,t}(o, β)` for `β ∈ 𝔅^N`. -/
theorem ofReal_trListWeight_mul_trStageMoment_eq_sum {o : ℤ × ℤ} (ho : o ∈ bkPoints) {N : ℕ}
    {β : List (List ℤ × ℤ)} (hlen : β.length = N) (hβ : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ))
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + N) (k t : ℕ) :
    ENNReal.ofReal (trListWeight β) * ENNReal.ofReal (trStageMoment n ξ G d k t o β) =
      ∑ q ∈ Finset.range (N + 1), ENNReal.ofReal (trListWeight β) *
        if trSublist β 1 q ∈ trFirstStopSet n ξ (epsStar : ℝ) o
        then ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o (trSublist β 1 q) q))) *
          ENNReal.ofReal (trStageMoment n ξ G d k t (trPath o (trSublist β 1 q) q)
            (trSublist β (q + 1) N))
        else 0 := by
  rw [← Finset.mul_sum]
  by_cases hlive : TrLive β
  · subst hlen
    rw [ofReal_trStageMoment_eq_sum_of_trLive ho hβ hlive hN k t]
  · simp [trListWeight_eq_zero_of_not_trLive hlive]

/-- After a first-stop list `u`, the remaining sum is a stage moment from a black origin, hence
bounded by `bw^⊗(u) max(b_*, (77/100)^d)^k`. -/
theorem tsum_trListWeight_mul_trStageMoment_of_mem_trFirstStopSet_le (hξ : IsResidueUnit ξ)
    {o : ℤ × ℤ} (ho : o ∈ bkPoints) {u : List (List ℤ × ℤ)}
    (hu : u ∈ trFirstStopSet n ξ (epsStar : ℝ) o) {b : ℕ}
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + ((u.length + b : ℕ) : ℤ)) (hd : 1 ≤ d) (k : ℕ) :
    ∑' f : {f : List (List ℤ × ℤ) // f.length = b ∧ ∀ x ∈ f, x.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight u) * ENNReal.ofReal (trListWeight f.1) *
          (ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o u u.length))) *
            ENNReal.ofReal (trStageMoment n ξ 4096 d k d (trPath o u u.length) f.1)) ≤
      ENNReal.ofReal (trListWeight u) *
        ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k) := by
  have hg := trPath_bkJ_sub_bkJ_ge o u (Nat.zero_le u.length)
  simp only [min_self, Nat.zero_min, trPath_zero, CharP.cast_eq_zero, sub_zero] at hg
  have hblack := trFirstStopSet_bkBlack hu
  have hxP := trPath_mem_bkPoints ho u u.length
  calc _ = ENNReal.ofReal (trListWeight u) *
          ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o u u.length))) *
          ∑' f : {f : List (List ℤ × ℤ) // f.length = b ∧ ∀ x ∈ f, x.2 ∈ ({4, 5} : Set ℤ)},
            ENNReal.ofReal (trListWeight f.1) *
              ENNReal.ofReal (trStageMoment n ξ 4096 d k d (trPath o u u.length) f.1) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun f => by ring
    _ ≤ ENNReal.ofReal (trListWeight u) * 1 *
          ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k) := by
        gcongr
        · refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 ?_))
          exact mul_nonneg (by exact_mod_cast gammaStar_pos.le) (trCount_nonneg _ _ _)
        · rw [tsum_trListWeight_mul_trStageMoment_eq_trStageMass 4096 d k d hxP hblack
            (by push_cast at hN; omega)]
          exact trStageMass_full_le hξ hxP hblack hd k
    _ = _ := by rw [mul_one]

open Classical in
/-- Splitting the sum over `β ∈ 𝔅^{q+b}` at `q`, the first-stop terms with stop `q` are bounded
by the weights of the first-stop lists of length `q`. -/
theorem tsum_trListWeight_mul_ite_trFirstStopSet_trStageMoment_le (hξ : IsResidueUnit ξ)
    {o : ℤ × ℤ} (ho : o ∈ bkPoints) {q b : ℕ}
    (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + ((q + b : ℕ) : ℤ)) (hd : 1 ≤ d) (k : ℕ) :
    ∑' β : {β : List (List ℤ × ℤ) // β.length = q + b ∧ ∀ x ∈ β, x.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) *
          (if trSublist β.1 1 q ∈ trFirstStopSet n ξ (epsStar : ℝ) o
          then ENNReal.ofReal
              (Real.exp (-((gammaStar : ℝ) * trCount n ξ o (trSublist β.1 1 q) q))) *
            ENNReal.ofReal (trStageMoment n ξ 4096 d k d (trPath o (trSublist β.1 1 q) q)
              (trSublist β.1 (q + 1) (q + b)))
          else 0) ≤
      ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧ ∀ x ∈ u, x.2 ∈ ({4, 5} : Set ℤ)},
        if u.1 ∈ trFirstStopSet n ξ (epsStar : ℝ) o then
          ENNReal.ofReal (trListWeight u.1) *
            ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k)
        else 0 := by
  refine le_of_eq_of_le (tsum_trListWeight_trSublist {c : List ℤ × ℤ | c.2 ∈ ({4, 5} : Set ℤ)}
    q b fun u f => if u ∈ trFirstStopSet n ξ (epsStar : ℝ) o then
      ENNReal.ofReal (Real.exp (-((gammaStar : ℝ) * trCount n ξ o u q))) *
        ENNReal.ofReal (trStageMoment n ξ 4096 d k d (trPath o u q) f) else 0) ?_
  refine ENNReal.tsum_le_tsum fun u => ?_
  obtain ⟨u, hul, -⟩ := u
  subst hul
  by_cases hu : u ∈ trFirstStopSet n ξ (epsStar : ℝ) o
  · simp only [hu, ↓reduceIte]
    exact tsum_trListWeight_mul_trStageMoment_of_mem_trFirstStopSet_le hξ ho hu hN hd k
  · simp only [hu, ↓reduceIte, mul_zero, tsum_zero, le_refl]

/-- **Discounted stages from any starting point.** Let `ξ ∈ G_n` be a unit, `o ∈ 𝒫`, `N ∈ ℕ`
with `j(o) + N > ⌊n/2⌋`, and `d ≥ 1`, `k ≥ 0` integers. Then
`∑_{β ∈ 𝔅^N} bw^⊗(β) 𝒵^{4096,d}_{k,d}(o, β) ≤ max(b_*, (77/100)^d)^k`. -/
@[collatz_pos_dens "lem_c3_stage_trace"]
theorem tsum_trListWeight_mul_trStageMoment_le (hξ : IsResidueUnit ξ) {o : ℤ × ℤ}
    (ho : o ∈ bkPoints) {N : ℕ} (hN : ((n / 2 : ℕ) : ℤ) < bkJ o + N) {d : ℕ} (hd : 1 ≤ d)
    (k : ℕ) :
    ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) *
          ENNReal.ofReal (trStageMoment n ξ 4096 d k d o β.1) ≤
      ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k) := by
  classical
  set C := ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k)
  set U := trFirstStopSet n ξ (epsStar : ℝ) o
  obtain ⟨F, hF⟩ : ∃ F : List (List ℤ × ℤ) → ℝ≥0∞, ∀ u,
      F u = if u ∈ U then ENNReal.ofReal (trListWeight u) * C else 0 :=
    ⟨_, fun _ => rfl⟩
  have hS := tsum_subtype_length_eq_tsum_ite (U := U) (G := F)
    (fun u hu => by rw [hF, ite_eq_right hu]) fun _ hu _ hb => trFirstStopSet_closing_mem hu hb
  have hmass : ∑' u : U, ENNReal.ofReal (trListWeight u.1) ≤ 1 :=
    tsum_trListWeight_le_one_of_prefixFree (n / 2) U
      (fun _ hu _ hb => trFirstStopSet_closing_mem hu hb)
      (fun _ hu => length_le_of_mem_trFirstStopSet ho hu) isPrefixFree_trFirstStopSet
  calc _ = ∑ q ∈ Finset.range (N + 1), ∑' β : {β : List (List ℤ × ℤ) // β.length = N ∧
          ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)}, ENNReal.ofReal (trListWeight β.1) *
          if trSublist β.1 1 q ∈ U
          then ENNReal.ofReal
              (Real.exp (-((gammaStar : ℝ) * trCount n ξ o (trSublist β.1 1 q) q))) *
            ENNReal.ofReal (trStageMoment n ξ 4096 d k d (trPath o (trSublist β.1 1 q) q)
              (trSublist β.1 (q + 1) N))
          else 0 := by
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact tsum_congr fun β =>
          ofReal_trListWeight_mul_trStageMoment_eq_sum ho β.2.1 β.2.2 hN k d
    _ ≤ ∑ q ∈ Finset.range (N + 1), ∑' u : {u : List (List ℤ × ℤ) // u.length = q ∧
          ∀ b ∈ u, b.2 ∈ ({4, 5} : Set ℤ)}, F u.1 := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨b, rfl⟩ : ∃ b, N = q + b := ⟨N - q, by simp at hq; omega⟩
        simpa only [hF] using tsum_trListWeight_mul_ite_trFirstStopSet_trStageMoment_le hξ ho hN
          hd k
    _ = ∑' u : List (List ℤ × ℤ), ∑ q ∈ Finset.range (N + 1),
          if u.length = q then F u else 0 := by
        simp_rw [hS]
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑' u : List (List ℤ × ℤ), F u := by
        refine ENNReal.tsum_le_tsum fun u => ?_
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp
    _ = ∑' u : U, ENNReal.ofReal (trListWeight u.1) * C := by
        rw [tsum_subtype U (fun u => ENNReal.ofReal (trListWeight u) * C)]
        refine tsum_congr fun u => ?_
        rw [hF, Set.indicator_apply]
    _ = (∑' u : U, ENNReal.ofReal (trListWeight u.1)) * C := ENNReal.tsum_mul_right
    _ ≤ 1 * C := by gcongr
    _ = C := one_mul C

end CollatzPosDens
