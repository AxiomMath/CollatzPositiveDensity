/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrListWeight
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The bridge mass

Fix a level `n` and a residue `ξ ∈ G_n`; points are coloured black or white at level `n`, residue
`ξ` and colour scale `ε_*`. For a base point `y ∈ 𝒫`, the *bridge mass* is the tilted weight of
the first-stop lists from `y`,
```
g_br(y) = ∑_{b ∈ 𝒰(y)} bw^⊗(b) e^{-γ_* N^*(y, b; |b|)} ∈ [0, ∞].
```
Each first-stop list `b` is weighted by its block weight `bw^⊗(b)` and tilted by the weighted
white count `N^*(y, b; |b|)` collected along its whole path. When `y` is itself black the only
first-stop list is the empty one and `g_br(y) = 1`.

## Main definitions

* `CollatzPosDens.trBridgeMass n ξ y`: the bridge mass `g_br(y) ∈ [0, ∞]`.

## Main results

* `CollatzPosDens.trBridgeMass_of_bkBlack`: `g_br(y) = 1` when `y` is black.
* `CollatzPosDens.trBridgeMass_le_tsum_trListWeight`: `g_br(y) ≤ ∑_{b ∈ 𝒰(y)} bw^⊗(b)`.

## Implementation notes

The sum ranges over the subtype of the set `𝒰(y)` (`CollatzPosDens.trFirstStopSet` at the
colour scale `ε_*`) and is the unconditional sum `tsum` in `[0, ∞]`, so it is always defined
and may be infinite. Each real factor enters through `ENNReal.ofReal`; both factors are
nonnegative, so nothing is truncated. The base point `y` ranges over all of `ℤ × ℤ`, which
generalizes `y ∈ 𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.5.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The bridge mass `g_br(y) = ∑_{b ∈ 𝒰(y)} bw^⊗(b) e^{-γ_* N^*(y, b; |b|)} ∈ [0, ∞]`, where
`𝒰(y)` is the set of first-stop lists from `y` at the colour scale `ε_*`. -/
@[collatz_pos_dens "def_tr_bridge_mass"]
noncomputable def trBridgeMass (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) : ℝ≥0∞ :=
  ∑' b : trFirstStopSet n ξ (epsStar : ℝ) y,
    ENNReal.ofReal (trListWeight b.1) *
      ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b.1 b.1.length))

variable {n : ℕ} {ξ : ResidueGroup n} {y : ℤ × ℤ}

/-- The bridge mass is the sum over first-stop lists `b ∈ 𝒰(y)` of
`bw^⊗(b) e^{-γ_* N^*(y, b; |b|)}`. -/
lemma trBridgeMass_def (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) :
    trBridgeMass n ξ y =
      ∑' b : trFirstStopSet n ξ (epsStar : ℝ) y,
        ENNReal.ofReal (trListWeight b.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b.1 b.1.length)) :=
  rfl

/-- The tilt factor `e^{-γ_* N^*(y, b; t)}` is at most `1`. -/
lemma trBridgeMass_exp_le_one (b : List (List ℤ × ℤ)) (t : ℕ) :
    Real.exp (-(gammaStar : ℝ) * trCount n ξ y b t) ≤ 1 := by
  rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
  exact mul_nonneg (by exact_mod_cast gammaStar_pos.le) (trCount_nonneg _ _ _)

/-- Each term of the bridge mass is at most the block weight of its list. -/
lemma trBridgeMass_term_le (b : List (List ℤ × ℤ)) (t : ℕ) :
    ENNReal.ofReal (trListWeight b) *
        ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b t)) ≤
      ENNReal.ofReal (trListWeight b) := by
  calc _ ≤ ENNReal.ofReal (trListWeight b) * 1 := by
        gcongr
        exact ENNReal.ofReal_le_one.2 (trBridgeMass_exp_le_one b t)
    _ = _ := mul_one _

/-- The bridge mass is at most the untilted weight `∑_{b ∈ 𝒰(y)} bw^⊗(b)`. -/
lemma trBridgeMass_le_tsum_trListWeight :
    trBridgeMass n ξ y ≤
      ∑' b : trFirstStopSet n ξ (epsStar : ℝ) y, ENNReal.ofReal (trListWeight b.1) :=
  ENNReal.tsum_le_tsum fun b ↦ trBridgeMass_term_le b.1 _

/-- If `y` is black, the empty list is the only first-stop list and `g_br(y) = 1`. -/
lemma trBridgeMass_of_bkBlack (hy : BkBlack n ξ (epsStar : ℝ) y) : trBridgeMass n ξ y = 1 := by
  rw [trBridgeMass_def, trFirstStopSet_eq_singleton_nil_of_bkBlack hy]
  exact (tsum_singleton ([] : List (List ℤ × ℤ)) fun b ↦ ENNReal.ofReal (trListWeight b) *
    ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b b.length))).trans (by simp)

end CollatzPosDens
