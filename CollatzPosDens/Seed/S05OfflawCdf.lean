/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Transfer.GeometricMass
public import Mathlib.Basic.Real.Basic

/-!
# The distribution function of the offset

For `D ∈ ℕ` and real `x`, the *offset distribution function* is the geometric mass
$$\mathsf F_D(x) = \mathbf p\bigl(\{u \in \mathbb Z_{\ge 1}^D : \mathrm{off}(u) \le x\}\bigr)
  \in [0, \infty]$$
of the words of length `D` whose offset is at most `x`. It is nondecreasing in `x`, and
`𝖥₀` is the indicator of `[0, ∞)`, the empty word having offset `0` and mass `1`.

## Main definitions

* `CollatzPosDens.offlawCdf D x`: the offset distribution function `𝖥_D(x) ∈ ℝ≥0∞`.

## Main results

* `CollatzPosDens.offlawCdf_def`: the defining formula.
* `CollatzPosDens.offlawCdf_mono`: `𝖥_D` is monotone.
* `CollatzPosDens.offlawCdf_zero`: `𝖥₀(x) = 1` if `0 ≤ x` and `0` otherwise.

## Implementation notes

The tuples `u ∈ ℤ_{≥1}^D` are the words (lists of positive naturals) of length `D`, and the
rational offset `off(u)` is compared with `x` after the cast to `ℝ`. The value lies in `ℝ≥0∞`,
as the geometric mass does.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- **Offset distribution function**: `𝖥_D(x) = 𝐩({u ∈ ℤ_{≥1}^D : off(u) ≤ x}) ∈ [0, ∞]`, the
geometric mass of the words of length `D` with offset at most `x`. -/
@[collatz_pos_dens "def_s05_offlaw_cdf"]
noncomputable def offlawCdf (D : ℕ) (x : ℝ) : ℝ≥0∞ :=
  geomMass {u : Word | u.length = D ∧ (off u : ℝ) ≤ x}

/-- `offlawCdf D x` is the geometric mass of the words of length `D` with offset at most `x`. -/
theorem offlawCdf_def (D : ℕ) (x : ℝ) :
    offlawCdf D x = geomMass {u : Word | u.length = D ∧ (off u : ℝ) ≤ x} := rfl

/-- The offset distribution function is nondecreasing in `x`. -/
theorem offlawCdf_mono (D : ℕ) : Monotone (offlawCdf D) := fun _ _ hxy =>
  geomMass_mono fun _ hu => ⟨hu.1, hu.2.trans hxy⟩

/-- `𝖥₀` is the indicator of `[0, ∞)`: the only word of length `0` is the empty word, of
offset `0` and geometric mass `1`. -/
theorem offlawCdf_zero (x : ℝ) : offlawCdf 0 x = if 0 ≤ x then 1 else 0 := by
  split_ifs with hx
  · have : {u : Word | u.length = 0 ∧ (off u : ℝ) ≤ x} = {[]} := by
      ext u
      simp only [Set.mem_ofPred_eq, List.length_eq_zero_iff, Set.mem_singleton_iff]
      exact ⟨And.left, fun h => ⟨h, by simp [h, hx]⟩⟩
    rw [offlawCdf_def, this]; simp
  · have : {u : Word | u.length = 0 ∧ (off u : ℝ) ≤ x} = ∅ := by
      ext u
      simp only [Set.mem_ofPred_eq, List.length_eq_zero_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl
      simpa using hx
    rw [offlawCdf_def, this]; simp

end CollatzPosDens
