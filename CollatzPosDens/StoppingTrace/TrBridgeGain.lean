/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPath
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The bridge gain

Fix a level `n`, a residue `ξ ∈ G_n` and the colour scale `ε_*`. For a base point `y ∈ 𝒫`, the
*bridge gain* is the bridge mass with each first-stop list `b ∈ 𝒰(y)` additionally weighted by the
positive part of the passage surplus at the gap of its endpoint,
```
H(y) = ∑_{b ∈ 𝒰(y)} bw^⊗(b) e^{-γ_* N^*(y, b; |b|)} max(δ_tr(gap(x_{|b|}(y, b))), 0) ∈ [0, ∞].
```

## Main definitions

* `CollatzPosDens.trBridgeGain n ξ y`: the bridge gain `H(y) ∈ [0, ∞]`.

## Main results

* `CollatzPosDens.trBridgeGain_le_mul_trBridgeMass`: if `δ_tr(gap(x_{|b|}(y, b))) ≤ c` for
  every `b ∈ 𝒰(y)`, then `H(y) ≤ c · g_br(y)`; this is the termwise comparison with the bridge
  mass.

## Implementation notes

The sum ranges over the subtype of the set `𝒰(y)` (`CollatzPosDens.trFirstStopSet` at the
colour scale `ε_*`) and is the unconditional sum `tsum` in `[0, ∞]`, so it is always defined
and may be infinite. Each real factor enters through `ENNReal.ofReal`; all three factors are
nonnegative (the last one by the explicit positive part), so nothing is truncated. The base
point `y` ranges over all of `ℤ × ℤ`, which generalizes `y ∈ 𝒫`.

## References

* [Mazur, *Collatz positive density*], §9.5.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The bridge gain
`H(y) = ∑_{b ∈ 𝒰(y)} bw^⊗(b) e^{-γ_* N^*(y, b; |b|)} max(δ_tr(gap(x_{|b|}(y, b))), 0) ∈ [0, ∞]`,
where `𝒰(y)` is the set of first-stop lists from `y` and the gap is taken at the colour scale
`ε_*`. -/
@[collatz_pos_dens "def_tr_bridge_gain"]
noncomputable def trBridgeGain (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) : ℝ≥0∞ :=
  ∑' b : trFirstStopSet n ξ (epsStar : ℝ) y,
    ENNReal.ofReal (trListWeight b.1) *
      ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b.1 b.1.length)) *
        ENNReal.ofReal
          (max (trDelta (trGap n ξ (epsStar : ℝ) (trPath y b.1 b.1.length))) 0)

variable {n : ℕ} {ξ : ResidueGroup n} {y : ℤ × ℤ}

/-- The bridge gain `H(y)` is the sum over first-stop lists `b ∈ 𝒰(y)` of
`bw^⊗(b) e^{-γ_* N^*(y, b; |b|)} max(δ_tr(gap(x_{|b|}(y, b))), 0)`. -/
lemma trBridgeGain_def (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) :
    trBridgeGain n ξ y =
      ∑' b : trFirstStopSet n ξ (epsStar : ℝ) y,
        ENNReal.ofReal (trListWeight b.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b.1 b.1.length)) *
            ENNReal.ofReal
              (max (trDelta (trGap n ξ (epsStar : ℝ) (trPath y b.1 b.1.length))) 0) :=
  rfl

/-- Termwise comparison with the bridge mass: if `δ_tr(gap(x_{|b|}(y, b))) ≤ c` for every
first-stop list `b ∈ 𝒰(y)`, then `H(y) ≤ c · g_br(y)`. -/
lemma trBridgeGain_le_mul_trBridgeMass {c : ℝ}
    (hc : ∀ b ∈ trFirstStopSet n ξ (epsStar : ℝ) y,
      trDelta (trGap n ξ (epsStar : ℝ) (trPath y b b.length)) ≤ c) :
    trBridgeGain n ξ y ≤ ENNReal.ofReal c * trBridgeMass n ξ y := by
  rw [trBridgeGain_def, trBridgeMass_def, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun b ↦ ?_
  rw [mul_comm (ENNReal.ofReal c)]
  refine mul_le_mul_right ?_ _
  refine ENNReal.ofReal_le_ofReal_iff'.2 ?_
  rcases le_total 0 c with h0 | h0
  · exact Or.inl (max_le (hc b.1 b.2) h0)
  · exact Or.inr (max_le ((hc b.1 b.2).trans h0) le_rfl)

/-- The bridge gain vanishes when the passage surplus is nonpositive at the endpoint of every
first-stop list. -/
lemma trBridgeGain_eq_zero_of_trDelta_nonpos
    (h : ∀ b ∈ trFirstStopSet n ξ (epsStar : ℝ) y,
      trDelta (trGap n ξ (epsStar : ℝ) (trPath y b b.length)) ≤ 0) :
    trBridgeGain n ξ y = 0 := by
  rw [trBridgeGain_def]
  refine ENNReal.tsum_eq_zero.2 fun b ↦ ?_
  rw [max_eq_right (h b.1 b.2), ENNReal.ofReal_zero, mul_zero]

end CollatzPosDens
