/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import CollatzPosDens.StoppingTrace.TrBridgeMassLe
public import CollatzPosDens.StoppingTrace.TrCountConcat
public import CollatzPosDens.StoppingTrace.TrEntrySplit
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrPassageBound
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# The bridge bound for one kernel step

Fix a level `n` and a unit `ξ ∈ G_n`; "black" and "white" refer to `(n, ξ, ε_*)`. For a point
`v` with `s = gap(v)`, every entry list from `v` splits uniquely as `π b` with `π ∈ Π_s` a passage
list and `b ∈ 𝒰(x_{|π|}(v, π))` a first-stop list. Block weights multiply and weighted white counts
add under this concatenation, so
```
m_1(v) = ∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)} g_br(x_{|π|}(v, π)),
```
and since `g_br ≤ 1` and every term is nonnegative this gives the bridge bound
```
m_1(v) ≤ ∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}.
```

## Main results

* `CollatzPosDens.trKernel_one_eq_tsum_trPassage_mul_trBridgeMass`: the passage decomposition
  of `m_1(v)`.
* `CollatzPosDens.trKernel_one_le_ofReal_tsum_trPassage`: the bridge bound
  `m_1(v) ≤ ∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}`.

## Implementation notes

The value `m_1(v)` lives in `[0, ∞]` while the passage series is a convergent series of
nonnegative reals, so the bound is stated against `ENNReal.ofReal` of the real sum. The gap is an
integer and `Π_s` is indexed by `s ∈ ℕ`, so the passage set is `Π_{gap(v).toNat}`; the gap is
nonnegative, so this is `Π_{gap(v)}`. The bound is stated for every `v ∈ ℤ × ℤ` and every `ξ`,
not only for black `v`, since the argument uses no property of `v`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n}

/-- **Passage decomposition of one kernel step.** For `s = gap(v)`,
`m_1(v) = ∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)} g_br(x_{|π|}(v, π))`. -/
theorem trKernel_one_eq_tsum_trPassage_mul_trBridgeMass (v : ℤ × ℤ) :
    trKernel n ξ 1 v =
      ∑' π : trPassage (trGap n ξ (epsStar : ℝ) v).toNat,
        ENNReal.ofReal (trListWeight π.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length)) *
            trBridgeMass n ξ (trPath v π.1 π.1.length) := by
  classical
  set s := (trGap n ξ (epsStar : ℝ) v).toNat
  set F : List (List ℤ × ℤ) → ℝ≥0∞ := fun u ↦
    ENNReal.ofReal (trListWeight u) *
      ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length)) with hF
  set S := {p : List (List ℤ × ℤ) × List (List ℤ × ℤ) | p.1 ∈ trPassage s ∧
        p.2 ∈ trFirstStopSet n ξ (epsStar : ℝ) (trPath v p.1 p.1.length)}
  have h1 : trKernel n ξ 1 v = ∑' u : trEntryWords n ξ (epsStar : ℝ) v, F u.1 := by
    rw [trKernel_succ]
    simp [hF]
  have h2 : ∑' u : trEntryWords n ξ (epsStar : ℝ) v, F u.1 = ∑' p : S, F (p.1.1 ++ p.1.2) :=
    (((trEntryWords_bijOn_append n ξ (epsStar : ℝ) v).equiv _).tsum_eq
      (fun u : trEntryWords n ξ (epsStar : ℝ) v ↦ F u.1)).symm
  have hfac : ∀ π b : List (List ℤ × ℤ), F (π ++ b) =
      (ENNReal.ofReal (trListWeight π) *
        ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length))) *
      (ENNReal.ofReal (trListWeight b) * ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) *
        trCount n ξ (trPath v π π.length) b b.length))) := by
    intro π b
    simp only [hF, trListWeight_append, List.length_append]
    rw [trCount_concat ξ v π b rfl, mul_add, Real.exp_add,
      ENNReal.ofReal_mul (trListWeight_nonneg _), ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  rw [h1, h2, tsum_subtype S (fun p ↦ F (p.1 ++ p.2)), tsum_subtype (trPassage s) (fun π ↦
    ENNReal.ofReal (trListWeight π) *
      ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length)) *
        trBridgeMass n ξ (trPath v π π.length))]
  refine (ENNReal.tsum_prod (f := fun a b ↦ S.indicator (fun p ↦ F (p.1 ++ p.2)) (a, b))).trans ?_
  refine tsum_congr fun π ↦ ?_
  by_cases hπ : π ∈ trPassage s
  · rw [Set.indicator_of_mem hπ, trBridgeMass_def, ← ENNReal.tsum_mul_left,
      tsum_subtype (trFirstStopSet n ξ (epsStar : ℝ) (trPath v π π.length)) (fun b ↦
        ENNReal.ofReal (trListWeight π) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π π.length)) *
          (ENNReal.ofReal (trListWeight b) * ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) *
            trCount n ξ (trPath v π π.length) b b.length))))]
    refine tsum_congr fun b ↦ ?_
    by_cases hb : b ∈ trFirstStopSet n ξ (epsStar : ℝ) (trPath v π π.length)
    · rw [Set.indicator_of_mem (show (π, b) ∈ S from ⟨hπ, hb⟩), Set.indicator_of_mem hb, hfac]
    · rw [Set.indicator_of_notMem (show (π, b) ∉ S from fun h ↦ hb h.2),
        Set.indicator_of_notMem hb]
  · rw [Set.indicator_of_notMem hπ]
    exact ENNReal.tsum_eq_zero.2 fun b ↦
      Set.indicator_of_notMem (show (π, b) ∉ S from fun h ↦ hπ h.1) _

/-- **Bridge bound.** For `s = gap(v)`,
`m_1(v) ≤ ∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}`. -/
@[collatz_pos_dens "lem_tr_bridge_positive"]
theorem trKernel_one_le_ofReal_tsum_trPassage (ξ : ResidueGroup n) (v : ℤ × ℤ) :
    trKernel n ξ 1 v ≤ ENNReal.ofReal (∑' π : trPassage (trGap n ξ (epsStar : ℝ) v).toNat,
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length)) := by
  set s := (trGap n ξ (epsStar : ℝ) v).toNat
  rw [trKernel_one_eq_tsum_trPassage_mul_trBridgeMass]
  calc _ ≤ ∑' π : trPassage s, ENNReal.ofReal
          (trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length)) := by
        refine ENNReal.tsum_le_tsum fun π ↦ ?_
        rw [ENNReal.ofReal_mul (trListWeight_nonneg _)]
        exact mul_le_of_le_one_right (by positivity) (trBridgeMass_le_one n ξ _)
    _ = _ :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun π ↦ mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le)
          (summable_trPassage_mul_exp_neg_trCount ξ v s)).symm

end CollatzPosDens
