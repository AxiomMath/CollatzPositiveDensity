/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPath
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Powers of the entry kernel

Fix a level `n` and a residue `ξ ∈ G_n`, and write `ε_*` for the colour scale
`CollatzPosDens.epsStar`. A point `v ∈ ℤ × ℤ` is *black* when `CollatzPosDens.BkBlack n ξ ε_* v`
holds. The *entry kernel* sends a black point `v` to the black points `x_{|u|}(v, u)` reached by
the entry lists `u ∈ 𝓔(v)`, with weight `bw^⊗(u) e^{-γ_* N^*(v, u; |u|)}`. Its powers applied to
the constant function `1` are the numbers `m_k(v) ∈ [0, ∞]`, defined by recursion on `k` for all
points at once: `m_0(v) = 1` and
```
m_{k+1}(v) = ∑_{u ∈ 𝓔(v)} bw^⊗(u) e^{-γ_* N^*(v, u; |u|)} m_k(x_{|u|}(v, u)).
```

## Main definitions

* `CollatzPosDens.trKernel n ξ k v`: the number `m_k(v) ∈ [0, ∞]`.

## Main results

* `CollatzPosDens.trKernel_zero`: `m_0(v) = 1`.
* `CollatzPosDens.trKernel_succ`: the recursion for `m_{k+1}(v)`.
* `CollatzPosDens.trKernel_succ_le`: `m_{k+1}(v) ≤ ∑_{u ∈ 𝓔(v)} bw^⊗(u) m_k(x_{|u|}(v, u))`.
* `CollatzPosDens.trKernel_succ_le_of_le`: `m_{k+1}(v)` is bounded by the recursion sum with `m_k`
  replaced by any upper bound `f` at the endpoints of entry lists.

## Implementation notes

The sum ranges over the subtype of the set `𝓔(v)` (`CollatzPosDens.trEntryWords` at the
colour scale `ε_*`) and is the unconditional sum `tsum` in `[0, ∞]`, so it is always defined and
may be infinite. The real factors `bw^⊗(u)` and `e^{-γ_* N^*}` enter through `ENNReal.ofReal`;
both are nonnegative, so nothing is truncated. The kernel is defined in [mazur2026] for black
points `v` only, but the recursion makes sense for every `v ∈ ℤ × ℤ`, and `m_{k+1}(v)` only
evaluates `m_k` at the black points `x_{|u|}(v, u)`, `u ∈ 𝓔(v)`; so the values at black points
agree with [mazur2026], and the definition on all of `ℤ × ℤ` is a generalization.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.5.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The powers of the entry kernel: `m_0(v) = 1` and
`m_{k+1}(v) = ∑_{u ∈ 𝓔(v)} bw^⊗(u) e^{-γ_* N^*(v, u; |u|)} m_k(x_{|u|}(v, u)) ∈ [0, ∞]`, where
`𝓔(v)` is the set of entry lists from `v` at the colour scale `ε_*`. -/
@[collatz_pos_dens "def_tr_kernel"]
noncomputable def trKernel (n : ℕ) (ξ : ResidueGroup n) : ℕ → ℤ × ℤ → ℝ≥0∞
  | 0, _ => 1
  | k + 1, v =>
    ∑' u : trEntryWords n ξ (epsStar : ℝ) v,
      ENNReal.ofReal (trListWeight u.1) *
        ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
          trKernel n ξ k (trPath v u.1 u.1.length)

variable {n : ℕ} {ξ : ResidueGroup n}

/-- `m_0(v) = 1`. -/
@[simp]
lemma trKernel_zero (v : ℤ × ℤ) : trKernel n ξ 0 v = 1 := rfl

/-- The recursion
`m_{k+1}(v) = ∑_{u ∈ 𝓔(v)} bw^⊗(u) e^{-γ_* N^*(v, u; |u|)} m_k(x_{|u|}(v, u))`. -/
lemma trKernel_succ (k : ℕ) (v : ℤ × ℤ) :
    trKernel n ξ (k + 1) v =
      ∑' u : trEntryWords n ξ (epsStar : ℝ) v,
        ENNReal.ofReal (trListWeight u.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
            trKernel n ξ k (trPath v u.1 u.1.length) :=
  rfl

/-- The tilt factor `e^{-γ_* N^*(v, u; t)}` is at most `1`. -/
lemma exp_neg_gammaStar_mul_trCount_le_one (v : ℤ × ℤ) (u : List (List ℤ × ℤ)) (t : ℕ) :
    Real.exp (-(gammaStar : ℝ) * trCount n ξ v u t) ≤ 1 := by
  rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
  exact mul_nonneg (by exact_mod_cast gammaStar_pos.le) (trCount_nonneg _ _ _)

/-- Dropping the tilt: `m_{k+1}(v) ≤ ∑_{u ∈ 𝓔(v)} bw^⊗(u) m_k(x_{|u|}(v, u))`. -/
lemma trKernel_succ_le (k : ℕ) (v : ℤ × ℤ) :
    trKernel n ξ (k + 1) v ≤
      ∑' u : trEntryWords n ξ (epsStar : ℝ) v,
        ENNReal.ofReal (trListWeight u.1) * trKernel n ξ k (trPath v u.1 u.1.length) := by
  rw [trKernel_succ]
  refine ENNReal.tsum_le_tsum fun u ↦ ?_
  calc _ ≤ ENNReal.ofReal (trListWeight u.1) * 1 * trKernel n ξ k (trPath v u.1 u.1.length) := by
        gcongr
        exact ENNReal.ofReal_le_one.2 (exp_neg_gammaStar_mul_trCount_le_one v u.1 _)
    _ = _ := by rw [mul_one]

/-- If `m_k ≤ f` at the endpoints `x_{|u|}(v, u)` of the entry lists `u ∈ 𝓔(v)`, then
`m_{k+1}(v)` is at most the same weighted sum with `m_k` replaced by `f`. -/
lemma trKernel_succ_le_of_le (k : ℕ) (v : ℤ × ℤ) (f : ℤ × ℤ → ℝ≥0∞)
    (hf : ∀ u ∈ trEntryWords n ξ (epsStar : ℝ) v,
      trKernel n ξ k (trPath v u u.length) ≤ f (trPath v u u.length)) :
    trKernel n ξ (k + 1) v ≤
      ∑' u : trEntryWords n ξ (epsStar : ℝ) v,
        ENNReal.ofReal (trListWeight u.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
            f (trPath v u.1 u.1.length) := by
  rw [trKernel_succ]
  exact ENNReal.tsum_le_tsum fun u ↦ by gcongr; exact hf u.1 u.2

end CollatzPosDens
