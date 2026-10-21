/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageTrace
public import CollatzPosDens.StoppingTrace.TrAtoms
public import CollatzPosDens.StoppingTrace.TrTraceEvent

/-!
# Discounted mass of atoms completing their stages

Fix a Fourier index `ι ∈ 𝔍`, a level `n`, put `J = ⌊n/2⌋` and fix a unit `ξ ∈ G_n`. Let `e ∈ 𝒫`,
let `d ≥ 1` and `k ≥ 0` be integers, `φ : ℕ × ℤ → [0, ∞)`, `D ⊆ ℕ × ℤ`, and let `S ⊆ 𝒜_n` be a
set of atoms such that every `a = ((r, ℓ), β) ∈ S` has `(r, ℓ) ∈ D` and its fresh path
`y = (y^e_u(a))_u` completes `k` stages (gap threshold `4096`, run length `d`) by the time
`P_*(ι) - 1`: the stage end index `se = se^{4096,d}_{k,d}(y; 1)` satisfies `se ≤ ν(y)` and
`τ_{se}(y) ≤ P_*(ι) - 1`. Then
```
∑_{a = ((r, ℓ), β) ∈ S} φ(r, ℓ) bw^⊗(β) exp(-γ_* N^e_{P_*(ι)-1}(a))
  ≤ max(b_*, (77/100)^d)^k ∑_{(r, ℓ) ∈ D} φ(r, ℓ).
```
Indeed, with `o_{r,ℓ} = (j(e) + r, l(e) + ℓ)`, the white count is monotone in time, so each summand
is at most `φ(r, ℓ) bw^⊗(β) 𝒵^{4096,d}_{k,d}(o_{r,ℓ}, β)`. All terms being nonnegative, `S` may be
enlarged to all atoms with `(r, ℓ) ∈ D`, and the sum then splits as
`∑_{(r, ℓ) ∈ D} φ(r, ℓ) ∑_{β ∈ 𝔅^J} bw^⊗(β) 𝒵^{4096,d}_{k,d}(o_{r,ℓ}, β)`. Since `j(o_{r,ℓ}) ≥ 1`,
`j(o_{r,ℓ}) + J > J`, so `CollatzPosDens.tsum_trListWeight_mul_trStageMoment_le` bounds each inner
sum by `max(b_*, (77/100)^d)^k`.

## Main results

* `CollatzPosDens.exp_neg_trWhiteCount_le_trStageMoment`: the pointwise bound
  `exp(-γ_* N^e_{P_*(ι)-1}(a)) ≤ 𝒵^{4096,d}_{k,d}(o_{r,ℓ}, β)` on the event.
* `CollatzPosDens.tsum_ofReal_mul_exp_neg_trWhiteCount_le_stageRate`: the bound above.

## Implementation notes

The sums are unconditional sums in `[0, ∞]`, the real terms entering through `ENNReal.ofReal`;
on nonnegative terms nothing is truncated, and no summability hypothesis is needed. The weight
`φ` is real-valued and its nonnegativity is not assumed: a negative value of `φ` contributes `0`
to both sides. The event `se ≤ ν(y)`, `τ_{se}(y) ≤ P_*(ι) - 1` is stated as: `se = i` for some
`i ∈ ℕ` with `τ_i(y) = s` defined and `s ≤ P_*(ι) - 1`; as `se ≥ 1`, the stopping time `τ_{se}(y)`
is defined exactly when `se ≤ ν(y)`, so the two formulations agree. The bound holds for every `n`,
including `n = 0`.

## References

* [Mazur, *Collatz positive density*], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- **The stage event bound.** If the fresh path `y = (y^e_u(a))_u` of `a = ((r, ℓ), β)` has stage
end index `se^{G,d}_{k,t}(y; 1) = i` with `τ_i(y) = s ≤ P_*(ι) - 1`, then
`exp(-γ_* N^e_{P_*(ι)-1}(a)) ≤ 𝒵^{G,d}_{k,t}(o, β)`, where `o = (j(e) + r, l(e) + ℓ)`. -/
theorem exp_neg_trWhiteCount_le_trStageMoment (ι : FIndex) {n : ℕ} (ξ : ResidueGroup n)
    (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) {G : ℤ} {d k t i s : ℕ}
    (hi : trStageEnd n ξ (epsStar : ℝ) G d (trFreshPath e a) k t 1 = i)
    (hs : trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) i = some s)
    (hsP : s ≤ pStar ι - 1) :
    Real.exp (-((gammaStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1))) ≤
      trStageMoment n ξ G d k t (bkJ e + a.1.1, bkL e + a.1.2) a.2 := by
  rw [trStageMoment_eq_of_trStopTime_eq_some hi hs, trWhiteCount_def, Real.exp_le_exp,
    neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (trCount_le_trCount _ _ _ _ hsP)
    (mod_cast gammaStar_pos.le)

/-- **Discounted mass of atoms completing their stages.** Let `ι ∈ 𝔍`, `ξ ∈ G_n` a unit,
`e ∈ 𝒫`, `d ≥ 1`, `k ∈ ℕ`, `φ : ℕ × ℤ → ℝ`, `D ⊆ ℕ × ℤ`, and `S ⊆ 𝒜_n` a set of atoms
`a = ((r, ℓ), β)` with `(r, ℓ) ∈ D` whose fresh path `y` has stage end index
`se = se^{4096,d}_{k,d}(y; 1) ≤ ν(y)` with `τ_{se}(y) ≤ P_*(ι) - 1`. Then
`∑_{a ∈ S} φ(r, ℓ) bw^⊗(β) exp(-γ_* N^e_{P_*(ι)-1}(a)) ≤
max(b_*, (77/100)^d)^k ∑_{(r, ℓ) ∈ D} φ(r, ℓ)`. -/
@[collatz_pos_dens "lem_c3_stage_discount"]
theorem tsum_ofReal_mul_exp_neg_trWhiteCount_le_stageRate (ι : FIndex) {n : ℕ}
    {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {e : ℤ × ℤ} (he : e ∈ bkPoints) {d : ℕ}
    (hd : 1 ≤ d) (k : ℕ) (φ : ℕ × ℤ → ℝ) (D : Set (ℕ × ℤ))
    (S : Set ((ℕ × ℤ) × List (List ℤ × ℤ))) (hS : S ⊆ trAtoms n) (hSD : ∀ a ∈ S, a.1 ∈ D)
    (hSse : ∀ a ∈ S, ∃ i s : ℕ,
      trStageEnd n ξ (epsStar : ℝ) 4096 d (trFreshPath e a) k d 1 = i ∧
        trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) i = some s ∧ s ≤ pStar ι - 1) :
    ∑' a : S, ENNReal.ofReal (φ a.1.1 * trListWeight a.1.2 *
        Real.exp (-((gammaStar : ℝ) * trWhiteCount n ξ e a.1 (pStar ι - 1)))) ≤
      ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k) *
        ∑' x : D, ENNReal.ofReal (φ x) := by
  classical
  set C := ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k)
  set B : Set (List (List ℤ × ℤ)) := {β | β.length = n / 2 ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)}
  set F : (ℕ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞ := fun x β =>
    D.indicator (fun x => ENNReal.ofReal (φ x)) x *
      B.indicator (fun β => ENNReal.ofReal (trListWeight β) *
        ENNReal.ofReal (trStageMoment n ξ 4096 d k d (bkJ e + x.1, bkL e + x.2) β)) β
  have hinner : ∀ x : ℕ × ℤ, ∑' β, B.indicator (fun β => ENNReal.ofReal (trListWeight β) *
      ENNReal.ofReal (trStageMoment n ξ 4096 d k d (bkJ e + x.1, bkL e + x.2) β)) β ≤ C := by
    intro x
    have he1 : (1 : ℤ) ≤ bkJ e := he
    have ho : ((bkJ e + x.1, bkL e + x.2) : ℤ × ℤ) ∈ bkPoints := by
      change (1 : ℤ) ≤ bkJ e + x.1
      omega
    have hN : ((n / 2 : ℕ) : ℤ) < bkJ (bkJ e + x.1, bkL e + x.2) + (n / 2 : ℕ) := by
      change ((n / 2 : ℕ) : ℤ) < bkJ e + x.1 + (n / 2 : ℕ)
      omega
    rw [← tsum_subtype B]
    exact tsum_trListWeight_mul_trStageMoment_le hξ ho hN hd k
  calc _ ≤ ∑' a : S, F a.1.1 a.1.2 := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        obtain ⟨⟨⟨r, ℓ⟩, β⟩, ha⟩ := a
        obtain ⟨i, s, hi, hs, hsP⟩ := hSse _ ha
        have hB : β ∈ B := hS ha
        have hD : (r, ℓ) ∈ D := hSD _ ha
        simp only [F, Set.indicator_of_mem hB, Set.indicator_of_mem hD]
        rw [ENNReal.ofReal_mul' (Real.exp_pos _).le, ENNReal.ofReal_mul' (trListWeight_nonneg _),
          mul_assoc]
        gcongr
        exact exp_neg_trWhiteCount_le_trStageMoment ι ξ e _ hi hs hsP
    _ ≤ ∑' a : (ℕ × ℤ) × List (List ℤ × ℤ), F a.1 a.2 :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun a : S => (a : (ℕ × ℤ) × List (List ℤ × ℤ)))
          Subtype.val_injective (fun a => F a.1 a.2)
    _ = ∑' x : ℕ × ℤ, ∑' β, F x β := ENNReal.tsum_prod
    _ = ∑' x : ℕ × ℤ, D.indicator (fun x => ENNReal.ofReal (φ x)) x *
          ∑' β, B.indicator (fun β => ENNReal.ofReal (trListWeight β) *
            ENNReal.ofReal (trStageMoment n ξ 4096 d k d (bkJ e + x.1, bkL e + x.2) β)) β := by
        simp only [F, ENNReal.tsum_mul_left]
    _ ≤ ∑' x : ℕ × ℤ, D.indicator (fun x => ENNReal.ofReal (φ x)) x * C := by
        gcongr with x
        exact hinner x
    _ = C * ∑' x : D, ENNReal.ofReal (φ x) := by
        rw [ENNReal.tsum_mul_right, mul_comm, tsum_subtype D (fun x => ENNReal.ofReal (φ x))]

end CollatzPosDens
