/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.BigOperators
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.DyadicReduction
public import CollatzPosDens.Transfer.ResidueMap
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxHeadGate

/-!
# The head mass `Hm_{n,k,l}`

For `n ≥ 1`, `k, l ∈ ℕ` and a residue `y ∈ G_n = ℤ/3^nℤ`, the *head mass* is the part of the
geometric mass of the head gate `Hd(n, k, l)` carried by the words whose offset reduces to `y`:
$$\mathrm{Hm}_{n,k,l}(y) = \sum_{h \in \mathrm{Hd}(n,k,l),\ [\mathrm{off}(h)]_n = y}
  2^{-A(h)}.$$
Since the head gate is finite, this is a finite sum of real numbers.

## Main definitions

* `CollatzPosDens.mxHeadMass`: the head mass `Hm_{n,k,l}(y)`.

## Main results

* `CollatzPosDens.mxHeadMass_def`: the defining finite sum.
* `CollatzPosDens.mxHeadMass_nonneg`: `0 ≤ Hm_{n,k,l}(y)`.
* `CollatzPosDens.ofReal_mxHeadMass`: `Hm_{n,k,l}(y)` is the submass
  `Sub^n_{Hd(n,k,l)}(y)`.
* `CollatzPosDens.mxHeadMass_eq_zero_of_mxHeadGate_eq_empty`: `Hm_{n,k,l} = 0` when
  `Hd(n, k, l) = ∅`.

## Implementation notes

The head mass is real-valued, as in the collision and convolution estimates that use it; the
sum runs over the finset `(mxHeadGate_finite n k l).toFinset` filtered by the condition
`[off(h)]_n = y`, where the offset is viewed as an element of `ℤ[1/2]` and reduced by
`dyadicRed n`; the weight `2^{-A(h)}` is written `2⁻¹ ^ A(h)`. The definition is stated for
every `n`; the hypothesis `n ≥ 1` belongs to the lemmas that use it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §13.1.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The head mass `Hm_{n,k,l}(y) = ∑_{h ∈ Hd(n,k,l), [off(h)]_n = y} 2^{-A(h)}`. -/
@[collatz_pos_dens "def_mx_head_mass"]
noncomputable def mxHeadMass (n k l : ℕ) (y : ResidueGroup n) : ℝ :=
  ∑ h ∈ (mxHeadGate_finite n k l).toFinset with
    dyadicRed n ⟨off h, off_mem_dyadicRationals h⟩ = y, (2⁻¹ : ℝ) ^ h.valSum

/-- Unfolding lemma for `mxHeadMass`. -/
theorem mxHeadMass_def (n k l : ℕ) (y : ResidueGroup n) :
    mxHeadMass n k l y =
      ∑ h ∈ (mxHeadGate_finite n k l).toFinset with
        dyadicRed n ⟨off h, off_mem_dyadicRationals h⟩ = y, (2⁻¹ : ℝ) ^ h.valSum :=
  rfl

/-- The head mass is nonnegative. -/
theorem mxHeadMass_nonneg (n k l : ℕ) (y : ResidueGroup n) : 0 ≤ mxHeadMass n k l y :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The head mass is the submass of the head gate: `Hm_{n,k,l}(y) = Sub^n_{Hd(n,k,l)}(y)`. -/
theorem ofReal_mxHeadMass (n k l : ℕ) (y : ResidueGroup n) :
    ENNReal.ofReal (mxHeadMass n k l y) = subMass n (mxHeadGate n k l) y := by
  rw [subMass_def]
  have hs : {w | w ∈ mxHeadGate n k l ∧ dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ = y} =
      (((mxHeadGate_finite n k l).toFinset.filter
        fun h => dyadicRed n ⟨off h, off_mem_dyadicRationals h⟩ = y : Finset Word) :
          Set Word) := by
    ext w; simp
  rw [hs, geomMass_coe_finset, mxHeadMass_def,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- If the head gate is empty, the head mass vanishes. -/
theorem mxHeadMass_eq_zero_of_mxHeadGate_eq_empty {n k l : ℕ} (h : mxHeadGate n k l = ∅)
    (y : ResidueGroup n) : mxHeadMass n k l y = 0 := by
  rw [mxHeadMass_def]
  refine Finset.sum_eq_zero fun w hw => ?_
  have : w ∈ mxHeadGate n k l := (Set.Finite.mem_toFinset _).1 (Finset.mem_filter.1 hw).1
  simp [h] at this

end CollatzPosDens
