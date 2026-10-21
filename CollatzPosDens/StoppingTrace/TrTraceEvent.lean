/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.S02Gamma
public import CollatzPosDens.StoppingTrace.TrCountMono
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrMoment
public import CollatzPosDens.StoppingTrace.TrWhiteCount

/-!
# The trace event bound

Let `ι ∈ 𝔍`, `e ∈ 𝒫`, `a = ((r, ℓ), β)` a fresh atom, `o = (j(e) + r, l(e) + ℓ)` and `k ∈ ℕ`,
and suppose that the stopping time `τ_{k+1}` of the fresh path `y = (y^e_t(a))_t` is defined
and at most `P_*(ι) - 1`. Then
`exp(-γ_* N^e_{P_*(ι)-1}(a)) ≤ 𝒵_{k+1}(o, β)`.

Indeed `y` is the path `x(o, β)`, so `𝒵_{k+1}(o, β) = exp(-γ_* N^*(o, β; τ_{k+1}(y)))`; the
weighted white count is nondecreasing in time, so
`N^*(o, β; τ_{k+1}(y)) ≤ N^*(o, β; P_*(ι) - 1) = N^e_{P_*(ι)-1}(a)`, and `γ_* > 0`.

## Main results

* `CollatzPosDens.exp_neg_trWhiteCount_le_trMoment`: the bound.

## Implementation notes

The hypothesis that the stopping sequence of `y` has at least `k + 1` terms and that
`τ_{k+1}(y) ≤ P_*(ι) - 1` is stated as `τ_{k+1}(y) = some t` with `t ≤ P_*(ι) - 1`, the stopping
time being an `Option ℕ` that is defined exactly when the sequence has at least `k + 1` terms.
The hypotheses `n ≥ 1`, `ξ` a unit, `e ∈ 𝒫` and `a ∈ 𝒜_n` are not needed, and `a` ranges over
the ambient type `(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n`.

## References

* [Mazur, *Collatz positive density*], §9.13, Discounted mass at the trace times and slow clearing.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The trace event bound.** Let `ι ∈ 𝔍`. If the stopping time `τ_{k+1}` of the fresh path
`y = (y^e_t(a))_t` is defined and at most `P_*(ι) - 1`, then
`exp(-γ_* N^e_{P_*(ι)-1}(a)) ≤ 𝒵_{k+1}(o, β)`, where `a = ((r, ℓ), β)` and
`o = (j(e) + r, l(e) + ℓ)`. -/
@[collatz_pos_dens "lem_tr_trace_event"]
theorem exp_neg_trWhiteCount_le_trMoment (ι : FIndex) {n : ℕ} (ξ : ResidueGroup n)
    (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) {k t : ℕ}
    (hτ : trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) (k + 1) = some t)
    (ht : t ≤ pStar ι - 1) :
    Real.exp (-((gammaStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1))) ≤
      trMoment n ξ (bkJ e + a.1.1, bkL e + a.1.2) a.2 (k + 1) := by
  rw [trMoment_eq_of_trStopTime_eq_some hτ, trWhiteCount_def, Real.exp_le_exp, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (trCount_le_trCount _ _ _ _ ht)
    (mod_cast gammaStar_pos.le)

end CollatzPosDens
