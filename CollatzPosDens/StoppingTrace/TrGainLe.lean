/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.StoppingTrace.TrBridgeGain
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrKernelOne
public import CollatzPosDens.StoppingTrace.TrPassageBound
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# The bridge gain is at most the bridge mass

Fix a level `n` and a unit `ξ ∈ G_n`; "black" and "white" refer to `(n, ξ, ε_*)`. For every
black point `w ∈ 𝒫` the passage surplus satisfies `δ_tr(gap(w)) ≤ 1 - d_*`, because the
one-passage series `∑_{π ∈ Π_{gap(w)}} bw^⊗(π) e^{-γ_* N^*(w, π; |π|)}` is nonnegative and is
bounded by `1 - d_* - δ_tr(gap(w))`. The endpoint `x_{|b|}(y, b)` of every first-stop list
`b ∈ 𝒰(y)` is black, so comparing the series defining the bridge gain and the bridge mass
termwise gives
```
H(y) ≤ (1 - d_*) g_br(y)        (y ∈ 𝒫).
```

## Main results

* `CollatzPosDens.trDelta_trGap_le_one_sub_dStar`: `δ_tr(gap(w)) ≤ 1 - d_*` for a black
  point `w ∈ 𝒫`.
* `CollatzPosDens.trBridgeGain_le`: `H(y) ≤ (1 - d_*) g_br(y)` for `y ∈ 𝒫`.

## Implementation notes

The kernel mass `m_1(w)` lives in `[0, ∞]` and its bound `m_1(w) ≤ 1 - d_* - δ_tr(gap(w))`
is stated through `ENNReal.ofReal`, which forgets the sign of a negative right-hand side, so
the inequality `δ_tr(gap(w)) ≤ 1 - d_*` is read off the real one-passage bound, whose
left-hand side is a sum of nonnegative reals. The positivity `1 - d_* > 0` is not needed: the
termwise comparison holds for any real constant. Both sides of the main result live in
`[0, ∞]`, with the factor `1 - d_*` entering through `ENNReal.ofReal`. No hypothesis `n ≥ 1`
or `J = ⌊n/2⌋` is needed.

## References

* [Mazur, *Collatz positive density*], §9.5.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n}

/-- At a black point `w ∈ 𝒫` the passage surplus is at most `1 - d_*`. -/
theorem trDelta_trGap_le_one_sub_dStar (hξ : IsResidueUnit ξ) {w : ℤ × ℤ} (hw : w ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) w) :
    trDelta (trGap n ξ (epsStar : ℝ) w) ≤ 1 - (dStar : ℝ) := by
  have h := tsum_trPassage_mul_exp_neg_trCount_le hξ hw hb
  have h0 : 0 ≤ ∑' π : trPassage (trGap n ξ (epsStar : ℝ) w),
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ w π.1 π.1.length) :=
    tsum_nonneg fun π ↦ mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le
  linarith

/-- **The bridge gain is at most the bridge mass.** Let `ξ ∈ G_n` be a unit. For every
`y ∈ 𝒫`, `H(y) ≤ (1 - d_*) g_br(y)`. -/
@[collatz_pos_dens "lem_tr_gain_le"]
theorem trBridgeGain_le (hξ : IsResidueUnit ξ) {y : ℤ × ℤ} (hy : y ∈ bkPoints) :
    trBridgeGain n ξ y ≤ ENNReal.ofReal (1 - (dStar : ℝ)) * trBridgeMass n ξ y :=
  trBridgeGain_le_mul_trBridgeMass fun b hb ↦
    trDelta_trGap_le_one_sub_dStar hξ (trPath_mem_bkPoints hy b _) (trFirstStopSet_bkBlack hb)

/-- At a point `y ∈ 𝒫` the bridge gain is finite. -/
theorem trBridgeGain_ne_top (hξ : IsResidueUnit ξ) {y : ℤ × ℤ} (hy : y ∈ bkPoints) :
    trBridgeGain n ξ y ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (trBridgeMass_ne_top n ξ y))
    (trBridgeGain_le hξ hy)

end CollatzPosDens
