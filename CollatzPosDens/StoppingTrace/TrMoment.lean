/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrTrace

/-!
# The weighted stop moment

Fix a level `n` and a residue `ξ ∈ G_n`; "black" and "white" refer to `(n, ξ, ε_*)`. For a base
point `o ∈ 𝒫`, a block list `β ∈ 𝔅^N`, the path `x = (x_t(o, β))_{t ∈ ℕ}` and `R ∈ ℕ`, the
*weighted stop moment* is
```
𝒵_R(o, β) = exp(-γ_* N^*(o, β; τ_R(x)))   if 1 ≤ R ≤ ν(x),
𝒵_R(o, β) = 0                             otherwise,
```
where `τ_R(x)` is the `R`-th stopping time of `x`, `ν(x)` the length of its stopping sequence,
`N^*(o, β; t)` the weighted white count and `γ_* = 87/200` the trace tilt.

## Main definitions

* `CollatzPosDens.trMoment n ξ o β R`: the weighted stop moment `𝒵_R(o, β)`.

## Main results

* `CollatzPosDens.trMoment_eq_of_trStopTime_eq_some`:
  `𝒵_R(o, β) = exp(-γ_* N^*(o, β; t))` when `τ_R(x) = t`.
* `CollatzPosDens.trMoment_eq_of_le`: the first case of the definition, for
  `1 ≤ R ≤ ν(x)`.
* `CollatzPosDens.trMoment_eq_zero_of_not`, `CollatzPosDens.trMoment_zero`:
  `𝒵_R(o, β) = 0` unless `1 ≤ R ≤ ν(x)`.
* `CollatzPosDens.trMoment_pos_iff`: `0 < 𝒵_R(o, β)` iff `1 ≤ R ≤ ν(x)`.
* `CollatzPosDens.trMoment_nonneg`, `CollatzPosDens.trMoment_le_one`:
  `0 ≤ 𝒵_R(o, β) ≤ 1`.

## Implementation notes

The stopping time `τ_R(x)` is an `Option ℕ`, which is `some` exactly when `1 ≤ R ≤ ν(x)`
(`CollatzPosDens.isSome_trStopTime_iff`); the moment is defined by cases on it, and
`CollatzPosDens.trMoment_eq_ite` restates it as a case split on `1 ≤ R ≤ ν(x)`. The stopping
sequence is taken at the colour scale `ε_*`. As for `CollatzPosDens.trPath`, the base point is
any `o ∈ ℤ × ℤ` and `β` any list of blocks; the length `N` is `β.length`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The weighted stop moment `𝒵_R(o, β)`: equal to `exp(-γ_* N^*(o, β; τ_R(x)))` when
`1 ≤ R ≤ ν(x)`, i.e. when the stopping time `τ_R(x)` of the path `x = x(o, β)` is defined, and
to `0` otherwise. The stopping sequence is that of `(n, ξ, ε_*)`. -/
@[collatz_pos_dens "def_tr_moment"]
noncomputable def trMoment (n : ℕ) (ξ : ResidueGroup n) (o : ℤ × ℤ) (β : List (List ℤ × ℤ))
    (R : ℕ) : ℝ :=
  (trStopTime n ξ (epsStar : ℝ) (trPath o β) R).elim 0
    fun t => Real.exp (-((gammaStar : ℝ) * trCount n ξ o β t))

variable {n : ℕ} {ξ : ResidueGroup n} {o : ℤ × ℤ} {β : List (List ℤ × ℤ)} {R t : ℕ}

/-- If `τ_R(x) = t`, then `𝒵_R(o, β) = exp(-γ_* N^*(o, β; t))`. -/
theorem trMoment_eq_of_trStopTime_eq_some
    (h : trStopTime n ξ (epsStar : ℝ) (trPath o β) R = some t) :
    trMoment n ξ o β R = Real.exp (-((gammaStar : ℝ) * trCount n ξ o β t)) := by
  rw [trMoment, h, Option.elim_some]

/-- If `τ_R(x)` is undefined, then `𝒵_R(o, β) = 0`. -/
theorem trMoment_eq_zero_of_trStopTime_eq_none
    (h : trStopTime n ξ (epsStar : ℝ) (trPath o β) R = none) :
    trMoment n ξ o β R = 0 := by
  rw [trMoment, h, Option.elim_none]

/-- For `1 ≤ R ≤ ν(x)`, `𝒵_R(o, β) = exp(-γ_* N^*(o, β; τ_R(x)))`, the stopping time `τ_R(x)`
being defined. -/
theorem trMoment_eq_of_le (h1 : 1 ≤ R) (h2 : R ≤ trNu n ξ (epsStar : ℝ) (trPath o β)) :
    trMoment n ξ o β R = Real.exp (-((gammaStar : ℝ) * trCount n ξ o β
      ((trStopTime n ξ (epsStar : ℝ) (trPath o β) R).get
        (isSome_trStopTime_iff.2 ⟨h1, h2⟩)))) :=
  trMoment_eq_of_trStopTime_eq_some (Option.some_get _).symm

/-- Unless `1 ≤ R ≤ ν(x)`, `𝒵_R(o, β) = 0`. -/
theorem trMoment_eq_zero_of_not (h : ¬(1 ≤ R ∧ R ≤ trNu n ξ (epsStar : ℝ) (trPath o β))) :
    trMoment n ξ o β R = 0 :=
  trMoment_eq_zero_of_trStopTime_eq_none
    (Option.not_isSome_iff_eq_none.1 fun h' => h (isSome_trStopTime_iff.1 h'))

/-- `𝒵_R(o, β)` as a case split on `1 ≤ R ≤ ν(x)`. -/
theorem trMoment_eq_ite :
    trMoment n ξ o β R =
      if h : 1 ≤ R ∧ R ≤ trNu n ξ (epsStar : ℝ) (trPath o β) then
        Real.exp (-((gammaStar : ℝ) * trCount n ξ o β
          ((trStopTime n ξ (epsStar : ℝ) (trPath o β) R).get (isSome_trStopTime_iff.2 h))))
      else 0 := by
  split_ifs with h
  · exact trMoment_eq_of_le h.1 h.2
  · exact trMoment_eq_zero_of_not h

/-- `𝒵_0(o, β) = 0`. -/
@[simp]
theorem trMoment_zero : trMoment n ξ o β 0 = 0 :=
  trMoment_eq_zero_of_trStopTime_eq_none trStopTime_zero

/-- The weighted stop moment is nonnegative. -/
theorem trMoment_nonneg : 0 ≤ trMoment n ξ o β R := by
  unfold trMoment
  cases trStopTime n ξ (epsStar : ℝ) (trPath o β) R
  · exact le_rfl
  · exact Real.exp_nonneg _

/-- The weighted stop moment is positive iff `1 ≤ R ≤ ν(x)`. -/
theorem trMoment_pos_iff :
    0 < trMoment n ξ o β R ↔ 1 ≤ R ∧ R ≤ trNu n ξ (epsStar : ℝ) (trPath o β) := by
  rw [← isSome_trStopTime_iff]
  unfold trMoment
  cases trStopTime n ξ (epsStar : ℝ) (trPath o β) R
  · simp
  · simpa using Real.exp_pos _

/-- The weighted stop moment is at most `1`, the weighted white count being nonnegative. -/
theorem trMoment_le_one : trMoment n ξ o β R ≤ 1 := by
  unfold trMoment
  cases trStopTime n ξ (epsStar : ℝ) (trPath o β) R with
  | none => exact zero_le_one
  | some t =>
    refine Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ?_ (trCount_nonneg _ _ _)))
    exact_mod_cast gammaStar_pos.le

end CollatzPosDens
