/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrAtoms
public import CollatzPosDens.StoppingTrace.TrLemma79
public import CollatzPosDens.StoppingTrace.TrTraceEvent

/-!
# Discounted mass of atoms with many trace times

Fix a Fourier index `ι ∈ 𝔍`, a level `n`, put `J = ⌊n/2⌋` and fix a unit `ξ ∈ G_n`. Let
`e ∈ 𝒫`, `k ∈ ℕ`, `φ : ℕ × ℤ → [0, ∞)`, `D ⊆ ℕ × ℤ`, and let `S ⊆ 𝒜_n` be a set of fresh atoms
such that every `a = ((r, ℓ), β) ∈ S` has `(r, ℓ) ∈ D` and the stopping time `τ_{k+1}` of the
fresh path `(y^e_t(a))_t` is defined and at most `P_*(ι) - 1`. Then
```
∑_{a = ((r, ℓ), β) ∈ S} φ(r, ℓ) bw^⊗(β) exp(-γ_* N^e_{P_*(ι)-1}(a))
  ≤ θ^en_k ∑_{(r, ℓ) ∈ D} φ(r, ℓ).
```
Indeed, with `o_{r,ℓ} = (j(e) + r, l(e) + ℓ)`, the trace event bound
`CollatzPosDens.exp_neg_trWhiteCount_le_trMoment` bounds each summand by
`φ(r, ℓ) bw^⊗(β) 𝒵_{k+1}(o_{r,ℓ}, β)`. All terms being nonnegative, `S` may be enlarged to all
atoms with `(r, ℓ) ∈ D`, and the sum then splits as
`∑_{(r, ℓ) ∈ D} φ(r, ℓ) ∑_{β ∈ 𝔅^J} bw^⊗(β) 𝒵_{k+1}(o_{r,ℓ}, β)`. Since `j(o_{r,ℓ}) ≥ 1`,
`j(o_{r,ℓ}) + J > J`, so `CollatzPosDens.tsum_trListWeight_mul_trMoment_le` bounds each inner
sum by `θ^en_k`.

## Main results

* `CollatzPosDens.tsum_ofReal_mul_exp_neg_trWhiteCount_le`: the bound above.

## Implementation notes

The sums are unconditional sums in `[0, ∞]`, the real terms entering through `ENNReal.ofReal`;
on nonnegative terms nothing is truncated, and no summability hypothesis is needed. The
weight `φ` is real-valued and its nonnegativity is not assumed: a negative value of `φ`
contributes `0` to both sides. The hypothesis that the stopping sequence of the fresh path has
at least `k + 1` terms, the `(k+1)`-st at most `P_*(ι) - 1`, is stated as
`τ_{k+1} = some t` with `t ≤ P_*(ι) - 1`. No hypothesis `n ≥ 1` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- **Discounted mass of atoms with many trace times.** Let `ι ∈ 𝔍`, `ξ ∈ G_n` a unit, `e ∈ 𝒫`,
`k ∈ ℕ`, `φ : ℕ × ℤ → ℝ`, `D ⊆ ℕ × ℤ`, and `S ⊆ 𝒜_n` a set of fresh atoms `a = ((r, ℓ), β)`
with `(r, ℓ) ∈ D` whose fresh path has its stopping time `τ_{k+1}` defined and at most
`P_*(ι) - 1`. Then
`∑_{a ∈ S} φ(r, ℓ) bw^⊗(β) exp(-γ_* N^e_{P_*(ι)-1}(a)) ≤ θ^en_k ∑_{(r, ℓ) ∈ D} φ(r, ℓ)`. -/
@[collatz_pos_dens "lem_tr_discounted_trace"]
theorem tsum_ofReal_mul_exp_neg_trWhiteCount_le (ι : FIndex) {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {e : ℤ × ℤ} (he : e ∈ bkPoints) (k : ℕ) (φ : ℕ × ℤ → ℝ)
    (D : Set (ℕ × ℤ)) (S : Set ((ℕ × ℤ) × List (List ℤ × ℤ))) (hS : S ⊆ trAtoms n)
    (hSD : ∀ a ∈ S, a.1 ∈ D)
    (hSτ : ∀ a ∈ S, ∃ t, trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) (k + 1) = some t ∧
      t ≤ pStar ι - 1) :
    ∑' a : S, ENNReal.ofReal (φ a.1.1 * trListWeight a.1.2 *
        Real.exp (-((gammaStar : ℝ) * trWhiteCount n ξ e a.1 (pStar ι - 1)))) ≤
      ENNReal.ofReal (thetaEn k : ℝ) * ∑' x : D, ENNReal.ofReal (φ x) := by
  classical
  set C := ENNReal.ofReal (thetaEn k : ℝ)
  set B : Set (List (List ℤ × ℤ)) := {β | β.length = n / 2 ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)}
  set F : (ℕ × ℤ) → List (List ℤ × ℤ) → ℝ≥0∞ := fun x β =>
    D.indicator (fun x => ENNReal.ofReal (φ x)) x *
      B.indicator (fun β => ENNReal.ofReal (trListWeight β) *
        ENNReal.ofReal (trMoment n ξ (bkJ e + x.1, bkL e + x.2) β (k + 1))) β
  have hinner : ∀ x : ℕ × ℤ, ∑' β, B.indicator (fun β => ENNReal.ofReal (trListWeight β) *
      ENNReal.ofReal (trMoment n ξ (bkJ e + x.1, bkL e + x.2) β (k + 1))) β ≤ C := by
    intro x
    have he1 : (1 : ℤ) ≤ bkJ e := he
    have ho : ((bkJ e + x.1, bkL e + x.2) : ℤ × ℤ) ∈ bkPoints := by
      change (1 : ℤ) ≤ bkJ e + x.1
      omega
    have hN : ((n / 2 : ℕ) : ℤ) < bkJ (bkJ e + x.1, bkL e + x.2) + (n / 2 : ℕ) := by
      change ((n / 2 : ℕ) : ℤ) < bkJ e + x.1 + (n / 2 : ℕ)
      omega
    rw [← tsum_subtype B]
    exact tsum_trListWeight_mul_trMoment_le hξ ho hN k
  calc _ ≤ ∑' a : S, F a.1.1 a.1.2 := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        obtain ⟨⟨⟨r, ℓ⟩, β⟩, ha⟩ := a
        obtain ⟨t, hτ, ht⟩ := hSτ _ ha
        have hB : β ∈ B := hS ha
        have hD : (r, ℓ) ∈ D := hSD _ ha
        simp only [F, Set.indicator_of_mem hB, Set.indicator_of_mem hD]
        rw [ENNReal.ofReal_mul' (Real.exp_pos _).le, ENNReal.ofReal_mul' (trListWeight_nonneg _),
          mul_assoc]
        gcongr
        exact exp_neg_trWhiteCount_le_trMoment ι ξ e _ hτ ht
    _ ≤ ∑' a : (ℕ × ℤ) × List (List ℤ × ℤ), F a.1 a.2 :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun a : S => (a : (ℕ × ℤ) × List (List ℤ × ℤ)))
          Subtype.val_injective (fun a => F a.1 a.2)
    _ = ∑' x : ℕ × ℤ, ∑' β, F x β := ENNReal.tsum_prod
    _ = ∑' x : ℕ × ℤ, D.indicator (fun x => ENNReal.ofReal (φ x)) x *
          ∑' β, B.indicator (fun β => ENNReal.ofReal (trListWeight β) *
            ENNReal.ofReal (trMoment n ξ (bkJ e + x.1, bkL e + x.2) β (k + 1))) β := by
        simp only [F, ENNReal.tsum_mul_left]
    _ ≤ ∑' x : ℕ × ℤ, D.indicator (fun x => ENNReal.ofReal (φ x)) x * C := by
        gcongr with x
        exact hinner x
    _ = C * ∑' x : D, ENNReal.ofReal (φ x) := by
        rw [ENNReal.tsum_mul_right, mul_comm, tsum_subtype D (fun x => ENNReal.ofReal (φ x))]

end CollatzPosDens
