/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3EntryLarge
public import CollatzPosDens.Case3.C3StageMass
public import CollatzPosDens.StoppingTrace.TrKernelOne
public import CollatzPosDens.Transfer.S02StageRate

/-!
# Mass of stopped stages

Fix a level `n` and a unit `ξ ∈ G_n`; "black" refers to `(n, ξ, ε_*)`. With the gap threshold
`G = 4096`, `a = 77/100` and `b_* = 333407/10⁶`, for every black point `v` and all integers
`d ≥ 1`, `k ≥ 1` and `1 ≤ t ≤ d`,
```
𝓜^{4096,d}_{k,t}(v) ≤ max(b_*, a^t) · max(b_*, a^d)^{k-1}.
```
Write `c = max(b_*, a^d)`. The proof is by induction on `(k, t)` in the lexicographic order, for
all black `v` at once. With `(k', t') = nx_{4096,d}(k, t; gap(v))`, the mass at the next state is
at most `B'` at every black point, where `B' = c^{k-1}` if `(k', t') = (k - 1, d)` (for `k = 1`
because `𝓜_{0,d} = 1`) and `B' = max(b_*, a^{t-1}) c^{k-1}` if `(k', t') = (k, t - 1)`; so
`𝓜^{4096,d}_{k,t}(v) ≤ B' m_1(v)`, where `m_1` is the first power of the entry kernel. If
`gap(v) ≥ 4096` then `m_1(v) < b_*` (`CollatzPosDens.trKernel_one_lt_stageRate`); otherwise
`m_1(v) ≤ 1 - d_entry = a` (`CollatzPosDens.trKernel_one_le`), and for `t ≥ 2` one uses
`a max(b_*, a^{t-1}) = max(a b_*, a^t) ≤ max(b_*, a^t)`.

## Main results

* `CollatzPosDens.trStageMass_le`: the bound above.
* `CollatzPosDens.trStageMass_full_le`: `𝓜^{4096,d}_{k,d}(v) ≤ max(b_*, (77/100)^d)^k` for every
  `k ≥ 0`.

## Implementation notes

The masses take values in `[0, ∞]`, and the real bound enters through `ENNReal.ofReal`. That `ξ`
is a unit, and that `v ∈ 𝒫`, the set on which blackness is defined, are explicit hypotheses. The
hypothesis `d ≥ 1` follows from `1 ≤ t ≤ d` and is not stated separately.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n}

/-- The induction step of the stopped-stage bound, for `k + 1` stages: if every mass with `k`
stages, at every state `1 ≤ t ≤ d` and every black point, is bounded as claimed, then so is every
mass with `k + 1` stages. -/
private theorem trStageMass_succ_le_of_le (hξ : IsResidueUnit ξ) {d k : ℕ}
    (ih : 1 ≤ k → ∀ t, 1 ≤ t → t ≤ d → ∀ w ∈ bkPoints, BkBlack n ξ (epsStar : ℝ) w →
      trStageMass n ξ 4096 d k t w ≤ ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ t) *
        max (stageRate : ℝ) ((77 / 100) ^ d) ^ (k - 1))) :
    ∀ t, 1 ≤ t → t ≤ d → ∀ v ∈ bkPoints, BkBlack n ξ (epsStar : ℝ) v →
      trStageMass n ξ 4096 d (k + 1) t v ≤ ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ t) *
        max (stageRate : ℝ) ((77 / 100) ^ d) ^ k) := by
  set b : ℝ := (stageRate : ℝ)
  set c : ℝ := max b ((77 / 100) ^ d)
  have hb : 0 < b := Rat.cast_pos.2 stageRate_pos
  have hc : 0 ≤ c := hb.le.trans (le_max_left _ _)
  have ha : 1 - (dEntry : ℝ) = 77 / 100 := by rw [dEntry_cast]; norm_num
  intro t ht htd
  have hfull : ∀ w ∈ bkPoints, BkBlack n ξ (epsStar : ℝ) w →
      trStageMass n ξ 4096 d k d w ≤ ENNReal.ofReal (c ^ k) := by
    intro w hw hwb
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · refine (ih hk d (ht.trans htd) le_rfl w hw hwb).trans_eq ?_
      rw [← pow_succ', Nat.sub_add_cancel hk]
  have hdone : ∀ t v, v ∈ bkPoints → BkBlack n ξ (epsStar : ℝ) v →
      trStageNext 4096 d (k + 1) t (trGap n ξ (epsStar : ℝ) v) = (k, d) →
      trStageMass n ξ 4096 d (k + 1) t v ≤ ENNReal.ofReal (c ^ k) * trKernel n ξ 1 v := by
    intro t v hv hvb hnx
    refine trStageMass_le_of_le (Nat.le_add_left 1 k) t v _ fun u hu => ?_
    rw [hnx]
    exact hfull _ (trPath_mem_bkPoints hv u _) (trEntryWords_bkBlack hu)
  induction t, ht using Nat.le_induction with
  | base =>
    intro v hv hvb
    have hnx : trStageNext 4096 d (k + 1) 1 (trGap n ξ (epsStar : ℝ) v) = (k, d) :=
      trStageNext_one
    by_cases hg : 4096 ≤ trGap n ξ (epsStar : ℝ) v
    · refine (hdone 1 v hv hvb hnx).trans ?_
      calc ENNReal.ofReal (c ^ k) * trKernel n ξ 1 v
          ≤ ENNReal.ofReal (c ^ k) * ENNReal.ofReal b := by
            gcongr; exact (trKernel_one_lt_stageRate hξ hv hvb hg).le
        _ = ENNReal.ofReal (b * c ^ k) := by
            rw [← ENNReal.ofReal_mul (pow_nonneg hc _), mul_comm]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _)
    · refine (hdone 1 v hv hvb hnx).trans ?_
      calc ENNReal.ofReal (c ^ k) * trKernel n ξ 1 v
          ≤ ENNReal.ofReal (c ^ k) * ENNReal.ofReal (77 / 100) := by
            gcongr; exact ha ▸ trKernel_one_le hξ hv hvb
        _ = ENNReal.ofReal (77 / 100 * c ^ k) := by
            rw [← ENNReal.ofReal_mul (pow_nonneg hc _), mul_comm]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr; simp)
  | succ t ht iht =>
    intro v hv hvb
    by_cases hg : 4096 ≤ trGap n ξ (epsStar : ℝ) v
    · refine (hdone (t + 1) v hv hvb (trStageNext_of_le hg)).trans ?_
      calc ENNReal.ofReal (c ^ k) * trKernel n ξ 1 v
          ≤ ENNReal.ofReal (c ^ k) * ENNReal.ofReal b := by
            gcongr; exact (trKernel_one_lt_stageRate hξ hv hvb hg).le
        _ = ENNReal.ofReal (b * c ^ k) := by
            rw [← ENNReal.ofReal_mul (pow_nonneg hc _), mul_comm]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _)
    · have hnx : trStageNext 4096 d (k + 1) (t + 1) (trGap n ξ (epsStar : ℝ) v) = (k + 1, t) :=
        trStageNext_of_lt (not_le.1 hg) (by omega)
      have hstep := trStageMass_le_of_le (Nat.le_add_left 1 k) (t + 1) v
        (ENNReal.ofReal (max b ((77 / 100) ^ t) * c ^ k)) fun u hu => by
          rw [hnx]
          exact iht (by omega) _ (trPath_mem_bkPoints hv u _) (trEntryWords_bkBlack hu)
      refine hstep.trans ?_
      calc ENNReal.ofReal (max b ((77 / 100) ^ t) * c ^ k) * trKernel n ξ 1 v
          ≤ ENNReal.ofReal (max b ((77 / 100) ^ t) * c ^ k) * ENNReal.ofReal (77 / 100) := by
            gcongr; exact ha ▸ trKernel_one_le hξ hv hvb
        _ = ENNReal.ofReal (77 / 100 * max b ((77 / 100) ^ t) * c ^ k) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            ring_nf
        _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hc _))
            rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 77 / 100), pow_succ']
            exact max_le_max (by linarith) le_rfl

/-- **Mass of stopped stages.** Let `ξ ∈ G_n` be a unit and `v ∈ 𝒫` a black point. For all
integers `k ≥ 1` and `1 ≤ t ≤ d`,
`𝓜^{4096,d}_{k,t}(v) ≤ max(b_*, (77/100)^t) · max(b_*, (77/100)^d)^{k-1}`. -/
@[collatz_pos_dens "lem_c3_stage_mass_bound"]
theorem trStageMass_le (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hvb : BkBlack n ξ (epsStar : ℝ) v) {d k t : ℕ} (hk : 1 ≤ k) (ht : 1 ≤ t) (htd : t ≤ d) :
    trStageMass n ξ 4096 d k t v ≤ ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ t) *
      max (stageRate : ℝ) ((77 / 100) ^ d) ^ (k - 1)) := by
  induction k, hk using Nat.le_induction generalizing t v with
  | base =>
    simpa using trStageMass_succ_le_of_le (k := 0) hξ (fun h => absurd h (by omega)) t ht htd v
      hv hvb
  | succ k hk ih =>
    rw [Nat.add_sub_cancel]
    exact trStageMass_succ_le_of_le hξ (fun _ t ht htd w hw hwb => ih hw hwb ht htd) t ht htd v
      hv hvb


/-- The stopped-stage masses with `k` stages at the full state `d` are at most
`max(b_*, (77/100)^d)^k` at black points. -/
theorem trStageMass_full_le (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hvb : BkBlack n ξ (epsStar : ℝ) v) {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    trStageMass n ξ 4096 d k d v ≤
      ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · refine (trStageMass_le hξ hv hvb hk hd le_rfl).trans_eq ?_
    rw [← pow_succ', Nat.sub_add_cancel hk]

end CollatzPosDens
