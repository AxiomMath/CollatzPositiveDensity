/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGeom4
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The exponential moment `M₄₅` of the horizontal law

For `t ∈ ℝ` we set `M₄₅(t) = ∑_{r ≥ 1} ν₄₅(r) e^{t r}`, a series of nonnegative terms whose
value lies in `[0, ∞]`.

## Main definitions

* `CollatzPosDens.mgfNu45`: the exponential moment `t ↦ ∑_{r ≥ 1} ν₄₅(r) e^{t r}`,
  valued in `ℝ≥0∞`.

## Main results

* `CollatzPosDens.mgfNu45_eq_tsum_int`: the value is the sum over all `r ∈ ℤ`, the terms
  with `r ≤ 0` vanishing.

## Implementation notes

The series is summed in `ℝ≥0∞`, so that `M₄₅` is total with values in `[0, ∞]`; each term
`ν₄₅(r) e^{tr} ≥ 0` is embedded by `ENNReal.ofReal`. The summation index `r ≥ 1` is written as
`r + 1` with `r : ℕ`.
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- The moment generating function `M₄₅(t) = ∑_{r ≥ 1} ν₄₅(r) e^{t r} ∈ [0, ∞]` of the
horizontal law `ν₄₅`. -/
@[collatz_pos_dens "def_rn_mgf"]
noncomputable def mgfNu45 (t : ℝ) : ℝ≥0∞ :=
  ∑' r : ℕ, ENNReal.ofReal (nu45 ((r : ℤ) + 1) * exp (t * ((r : ℝ) + 1)))

/-- Unfolding lemma for `mgfNu45`. -/
lemma mgfNu45_def (t : ℝ) :
    mgfNu45 t = ∑' r : ℕ, ENNReal.ofReal (nu45 ((r : ℤ) + 1) * exp (t * ((r : ℝ) + 1))) := rfl

/-- `M₄₅(t)` as a sum over all `r ∈ ℤ`; the terms with `r ≤ 0` vanish. -/
lemma mgfNu45_eq_tsum_int (t : ℝ) :
    mgfNu45 t = ∑' r : ℤ, ENNReal.ofReal (nu45 r * exp (t * (r : ℝ))) := by
  have hinj : Function.Injective (fun k : ℕ ↦ (k : ℤ) + 1) := fun a b h ↦ by simpa using h
  rw [mgfNu45_def, ← hinj.tsum_eq]
  · congr 1
    ext r
    simp
  · intro j hj
    by_contra hr
    have : j ≤ 0 := by
      by_contra h
      exact hr ⟨(j - 1).toNat, by simp only; omega⟩
    simp [nu45_of_nonpos this] at hj

end CollatzPosDens
