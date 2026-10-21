/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageEnd
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.S02Gamma
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The discount at the end of the stages

Fix a level `n` and a residue `ξ ∈ G_n`; the stopping sequence is that of `(n, ξ, ε_*)`. For a
base point `o ∈ 𝒫`, a block list `β ∈ 𝔅^N`, the path `x = (x_u(o, β))_{u ∈ ℕ}`, a gap threshold
`G ≥ 0`, a run length `d ≥ 1`, and integers `k ≥ 0` and `1 ≤ t ≤ d`, the *discount at the end of
the stages* is
```
𝒵^{G,d}_{k,t}(o, β) = exp(-γ_* N^*(o, β; τ_{se}(x)))   if se = se^{G,d}_{k,t}(x; 1) ≤ ν(x),
𝒵^{G,d}_{k,t}(o, β) = 0                                otherwise,
```
where `se^{G,d}_{k,t}(x; 1)` is the stage end index, `τ_i(x)` the `i`-th stopping time of `x`,
`N^*(o, β; t)` the weighted white count and `γ_* = 133/3125` the trace tilt.

## Main definitions

* `CollatzPosDens.trStageMoment n ξ G d k t o β`: the discount `𝒵^{G,d}_{k,t}(o, β)`.

## Main results

* `CollatzPosDens.trStageMoment_eq_of_trStopTime_eq_some`: if `se^{G,d}_{k,t}(x; 1) = i` and
  `τ_i(x) = s`, then `𝒵^{G,d}_{k,t}(o, β) = exp(-γ_* N^*(o, β; s))`.
* `CollatzPosDens.trStageMoment_eq_zero_of_trStopTime_eq_none`: `𝒵^{G,d}_{k,t}(o, β) = 0` if
  `se^{G,d}_{k,t}(x; 1) = i` and `τ_i(x)` is undefined.
* `CollatzPosDens.trStageMoment_eq_zero_of_trNu_lt`: `𝒵^{G,d}_{k,t}(o, β) = 0` when
  `ν(x) < se^{G,d}_{k,t}(x; 1)`.
* `CollatzPosDens.trStageMoment_nonneg`, `CollatzPosDens.trStageMoment_le_one`:
  `0 ≤ 𝒵^{G,d}_{k,t}(o, β) ≤ 1`.

## Implementation notes

The stage end index lies in `ℕ∞`, and the comparison `se ≤ ν(x)` is made there; when it holds,
`se` is a natural number `≥ 1` at most `ν(x)`, so the stopping time `τ_{se}(x)`, an `Option ℕ`,
is defined, and the definition evaluates it with `Option.elim` (whose default value `0` is never
used). As for `CollatzPosDens.trPath`, the base point is any `o ∈ ℤ × ℤ` and `β` any list of
blocks, the length `N` being `β.length`; the threshold `G` is any integer and `t` any natural
number.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The discount at the end of the stages: `𝒵^{G,d}_{k,t}(o, β) = exp(-γ_* N^*(o, β; τ_{se}(x)))`
if the stage end index `se = se^{G,d}_{k,t}(x; 1)` of the path `x = x(o, β)` is at most `ν(x)`,
and `0` otherwise. The stopping sequence is that of `(n, ξ, ε_*)`. -/
@[collatz_pos_dens "def_c3_stage_moment"]
noncomputable def trStageMoment (n : ℕ) (ξ : ResidueGroup n) (G : ℤ) (d k t : ℕ) (o : ℤ × ℤ)
    (β : List (List ℤ × ℤ)) : ℝ :=
  if trStageEnd n ξ (epsStar : ℝ) G d (trPath o β) k t 1 ≤ trNu n ξ (epsStar : ℝ) (trPath o β)
  then
    (trStopTime n ξ (epsStar : ℝ) (trPath o β)
      (trStageEnd n ξ (epsStar : ℝ) G d (trPath o β) k t 1).toNat).elim 0
      fun s => Real.exp (-((gammaStar : ℝ) * trCount n ξ o β s))
  else 0

variable {n : ℕ} {ξ : ResidueGroup n} {G : ℤ} {d k t : ℕ} {o : ℤ × ℤ} {β : List (List ℤ × ℤ)}

/-- If the stage end index is `se^{G,d}_{k,t}(x; 1) = i` and `τ_i(x) = s`, then
`𝒵^{G,d}_{k,t}(o, β) = exp(-γ_* N^*(o, β; s))`. -/
theorem trStageMoment_eq_of_trStopTime_eq_some {i s : ℕ}
    (hi : trStageEnd n ξ (epsStar : ℝ) G d (trPath o β) k t 1 = i)
    (hs : trStopTime n ξ (epsStar : ℝ) (trPath o β) i = some s) :
    trStageMoment n ξ G d k t o β = Real.exp (-((gammaStar : ℝ) * trCount n ξ o β s)) := by
  have hle : i ≤ trNu n ξ (epsStar : ℝ) (trPath o β) :=
    (isSome_trStopTime_iff.1 (by rw [hs]; rfl)).2
  rw [trStageMoment, hi, ite_eq_left (by exact_mod_cast hle), ENat.toNat_natCast, hs,
    Option.elim_some]

/-- If the stage end index is `se^{G,d}_{k,t}(x; 1) = i` and `τ_i(x)` is undefined, then
`𝒵^{G,d}_{k,t}(o, β) = 0`. -/
theorem trStageMoment_eq_zero_of_trStopTime_eq_none {i : ℕ}
    (hi : trStageEnd n ξ (epsStar : ℝ) G d (trPath o β) k t 1 = i)
    (hs : trStopTime n ξ (epsStar : ℝ) (trPath o β) i = none) :
    trStageMoment n ξ G d k t o β = 0 := by
  rw [trStageMoment, hi, ENat.toNat_natCast, hs, Option.elim_none, ite_self]

/-- If `ν(x) < se^{G,d}_{k,t}(x; 1)`, then `𝒵^{G,d}_{k,t}(o, β) = 0`. -/
theorem trStageMoment_eq_zero_of_trNu_lt
    (h : (trNu n ξ (epsStar : ℝ) (trPath o β) : ℕ∞) <
      trStageEnd n ξ (epsStar : ℝ) G d (trPath o β) k t 1) :
    trStageMoment n ξ G d k t o β = 0 := by
  rw [trStageMoment, ite_eq_right (not_le.2 h)]

/-- If `se^{G,d}_{k,t}(x; 1) = ∞`, then `𝒵^{G,d}_{k,t}(o, β) = 0`. -/
theorem trStageMoment_eq_zero_of_eq_top
    (h : trStageEnd n ξ (epsStar : ℝ) G d (trPath o β) k t 1 = ⊤) :
    trStageMoment n ξ G d k t o β = 0 :=
  trStageMoment_eq_zero_of_trNu_lt (h ▸ ENat.natCast_lt_top _)

/-- The discount at the end of the stages is nonnegative. -/
theorem trStageMoment_nonneg : 0 ≤ trStageMoment n ξ G d k t o β := by
  unfold trStageMoment
  split_ifs
  · cases trStopTime n ξ (epsStar : ℝ) (trPath o β)
      (trStageEnd n ξ (epsStar : ℝ) G d (trPath o β) k t 1).toNat
    · exact le_rfl
    · exact (Real.exp_pos _).le
  · exact le_rfl

/-- The discount at the end of the stages is at most `1`, the weighted white count being
nonnegative. -/
theorem trStageMoment_le_one : trStageMoment n ξ G d k t o β ≤ 1 := by
  unfold trStageMoment
  split_ifs
  · cases trStopTime n ξ (epsStar : ℝ) (trPath o β)
      (trStageEnd n ξ (epsStar : ℝ) G d (trPath o β) k t 1).toNat
    · exact zero_le_one
    · exact Real.exp_le_one_iff.2
        (neg_nonpos.2 (mul_nonneg (mod_cast gammaStar_pos.le) (trCount_nonneg _ _ _)))
  · exact zero_le_one

end CollatzPosDens
