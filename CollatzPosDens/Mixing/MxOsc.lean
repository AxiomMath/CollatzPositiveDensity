/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxFiberAvg

/-!
# Oscillation about the fibre average

For `0 ≤ m ≤ n` and `c : G_n → ℝ`, where `G_n = CollatzPosDens.ResidueGroup n`, the oscillation
of `c` at scale `m` is the `ℓ¹` distance of `c` from its fibre average
`Avg_{m,n} c = CollatzPosDens.fiberAvg h c`:
`Osc_{m,n}(c) = ∑_{y ∈ G_n} |c(y) - Avg_{m,n} c (y)|`.
It vanishes when `m = n` and on constant functions, and is always nonnegative.

## Main definitions

* `CollatzPosDens.oscillation h c`: for `h : m ≤ n`, the oscillation `Osc_{m,n}(c)`.

## Main results

* `CollatzPosDens.oscillation_nonneg`: `0 ≤ Osc_{m,n}(c)`.
* `CollatzPosDens.oscillation_self`: `Osc_{n,n}(c) = 0`.
* `CollatzPosDens.oscillation_const`: the oscillation of a constant function is `0`.

## Implementation notes

As for `CollatzPosDens.fiberAvg`, the hypothesis `m ≤ n` is an explicit proof argument.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.1.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `h : m ≤ n`, the oscillation of `c : G_n → ℝ` about its fibre average:
`Osc_{m,n}(c) = ∑_{y ∈ G_n} |c(y) - Avg_{m,n} c (y)|`. -/
@[collatz_pos_dens "def_mx_osc"]
noncomputable def oscillation {m n : ℕ} (h : m ≤ n) (c : ResidueGroup n → ℝ) : ℝ :=
  ∑ y, |c y - fiberAvg h c y|

/-- The oscillation is nonnegative. -/
theorem oscillation_nonneg {m n : ℕ} (h : m ≤ n) (c : ResidueGroup n → ℝ) :
    0 ≤ oscillation h c :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- The oscillation at the top scale `m = n` vanishes. -/
@[simp]
theorem oscillation_self {n : ℕ} (c : ResidueGroup n → ℝ) :
    oscillation (le_refl n) c = 0 := by
  simp [oscillation]

/-- The oscillation of a constant function vanishes. -/
@[simp]
theorem oscillation_const {m n : ℕ} (h : m ≤ n) (a : ℝ) :
    oscillation h (fun _ : ResidueGroup n => a) = 0 := by
  simp [oscillation]

end CollatzPosDens
