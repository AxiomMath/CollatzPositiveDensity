/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageNext
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrKernel

/-!
# Stopped-stage masses

Fix a level `n` and a residue `ξ ∈ G_n`; a point `v ∈ ℤ × ℤ` is *black* when
`CollatzPosDens.BkBlack n ξ ε_* v` holds. For a gap threshold `G ≥ 0` and a run length `d ≥ 1`,
the *stopped-stage masses* `𝓜^{G,d}_{k,t}(v) ∈ [0, ∞]`, for black points `v`, integers `k ≥ 0`
and `1 ≤ t ≤ d`, are defined by recursion on `(k, t)` in the lexicographic order, for all black
points at once: `𝓜^{G,d}_{0,t}(v) = 1` and, for `k ≥ 1`,
```
𝓜^{G,d}_{k,t}(v) = ∑_{u ∈ 𝓔(v)} bw^⊗(u) e^{-γ_* N^*(v, u; |u|)}
  𝓜^{G,d}_{nx_{G,d}(k, t; gap(v))}(x_{|u|}(v, u)),
```
where `𝓔(v)` is the set `CollatzPosDens.trEntryWords n ξ ε_* v` of entry lists from `v`,
`gap(v)` is `CollatzPosDens.trGap n ξ ε_* v`, and `nx_{G,d}` is the next state
`CollatzPosDens.trStageNext G d` of a stage. Thus `𝓜^{G,d}_{k,t}(v)` is the entry kernel
iterated until `k` stages are complete, a stage being complete at the first departure from a
point of gap at least `G`, or at the `d`-th departure from points of gap less than `G` (the first
stage allowing only `t` of them).

## Main definitions

* `CollatzPosDens.trStageMass n ξ G d k t v`: the stopped-stage mass `𝓜^{G,d}_{k,t}(v)`.

## Main results

* `CollatzPosDens.trStageMass_zero`: `𝓜^{G,d}_{0,t}(v) = 1`.
* `CollatzPosDens.trStageMass_of_one_le`: the recursion for `k ≥ 1`.
* `CollatzPosDens.trStageMass_le_of_le`: if `𝓜` at the next state is at most `B` at the endpoints
  of the entry lists, then `𝓜^{G,d}_{k,t}(v) ≤ B m_1(v)`, `m_1` the first power of the entry
  kernel.

## Implementation notes

The masses are defined for all `t ∈ ℕ` and all `v ∈ ℤ × ℤ`, by well-founded recursion on
`(k, t)` in the lexicographic order (`CollatzPosDens.trStageNext_lt`); on black `v` and
`1 ≤ t ≤ d` they are the masses described above, the recursion only evaluating masses at black
points and at states with second coordinate in `{1, …, d}`. As for `CollatzPosDens.trKernel`, the
sum is the unconditional sum in `[0, ∞]`, and the real factors enter through `ENNReal.ofReal`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The stopped-stage masses `𝓜^{G,d}_{k,t}(v) ∈ [0, ∞]`: `𝓜^{G,d}_{0,t}(v) = 1` and, for
`k ≥ 1`, `𝓜^{G,d}_{k,t}(v) = ∑_{u ∈ 𝓔(v)} bw^⊗(u) e^{-γ_* N^*(v, u; |u|)}
𝓜^{G,d}_{nx_{G,d}(k,t;gap(v))}(x_{|u|}(v, u))`, by recursion on `(k, t)` in the lexicographic
order. -/
@[collatz_pos_dens "def_c3_stage_mass"]
noncomputable def trStageMass (n : ℕ) (ξ : ResidueGroup n) (G : ℤ) (d : ℕ) :
    ℕ → ℕ → ℤ × ℤ → ℝ≥0∞
  | 0, _, _ => 1
  | k + 1, t, v =>
    ∑' u : trEntryWords n ξ (epsStar : ℝ) v,
      ENNReal.ofReal (trListWeight u.1) *
        ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
          trStageMass n ξ G d (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).1
            (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).2
            (trPath v u.1 u.1.length)
termination_by k t _ => (k, t)
decreasing_by exact trStageNext_lt (Nat.le_add_left 1 k)

variable {n : ℕ} {ξ : ResidueGroup n} {G : ℤ} {d : ℕ}

/-- `𝓜^{G,d}_{0,t}(v) = 1`. -/
@[simp]
theorem trStageMass_zero (t : ℕ) (v : ℤ × ℤ) : trStageMass n ξ G d 0 t v = 1 := by
  rw [trStageMass]

/-- The recursion `𝓜^{G,d}_{k+1,t}(v) = ∑_{u ∈ 𝓔(v)} bw^⊗(u) e^{-γ_* N^*(v, u; |u|)}
𝓜^{G,d}_{nx_{G,d}(k+1,t;gap(v))}(x_{|u|}(v, u))`. -/
theorem trStageMass_succ (k t : ℕ) (v : ℤ × ℤ) :
    trStageMass n ξ G d (k + 1) t v =
      ∑' u : trEntryWords n ξ (epsStar : ℝ) v,
        ENNReal.ofReal (trListWeight u.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
            trStageMass n ξ G d (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).1
              (trStageNext G d (k + 1) t (trGap n ξ (epsStar : ℝ) v)).2
              (trPath v u.1 u.1.length) := by
  rw [trStageMass]

/-- The recursion for `k ≥ 1`: `𝓜^{G,d}_{k,t}(v) = ∑_{u ∈ 𝓔(v)} bw^⊗(u)
e^{-γ_* N^*(v, u; |u|)} 𝓜^{G,d}_{nx_{G,d}(k,t;gap(v))}(x_{|u|}(v, u))`. -/
theorem trStageMass_of_one_le {k : ℕ} (hk : 1 ≤ k) (t : ℕ) (v : ℤ × ℤ) :
    trStageMass n ξ G d k t v =
      ∑' u : trEntryWords n ξ (epsStar : ℝ) v,
        ENNReal.ofReal (trListWeight u.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
            trStageMass n ξ G d (trStageNext G d k t (trGap n ξ (epsStar : ℝ) v)).1
              (trStageNext G d k t (trGap n ξ (epsStar : ℝ) v)).2
              (trPath v u.1 u.1.length) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  exact trStageMass_succ k t v

/-- If the mass at the next state `(k', t') = nx_{G,d}(k, t; gap(v))` is at most `B` at the
endpoints `x_{|u|}(v, u)` of the entry lists `u ∈ 𝓔(v)`, then `𝓜^{G,d}_{k,t}(v) ≤ B m_1(v)`,
where `m_1` is the first power of the entry kernel. -/
theorem trStageMass_le_of_le {k : ℕ} (hk : 1 ≤ k) (t : ℕ) (v : ℤ × ℤ) (B : ℝ≥0∞)
    (hB : ∀ u ∈ trEntryWords n ξ (epsStar : ℝ) v,
      trStageMass n ξ G d (trStageNext G d k t (trGap n ξ (epsStar : ℝ) v)).1
        (trStageNext G d k t (trGap n ξ (epsStar : ℝ) v)).2 (trPath v u u.length) ≤ B) :
    trStageMass n ξ G d k t v ≤ B * trKernel n ξ 1 v := by
  rw [trStageMass_of_one_le hk, trKernel_succ, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun u => ?_
  rw [trKernel_zero, mul_one, mul_comm B]
  exact mul_le_mul_right (hB u.1 u.2) _

end CollatzPosDens
