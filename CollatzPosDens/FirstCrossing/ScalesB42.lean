/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Scales
public import Mathlib.Logic.Function.Iterate

/-!
# The scale `b_42 = 256`

The scales `b_j` are given by `b_0 = 9` and `b_{j+1} = b_j + e_{b_j}`. Evaluating this
recursion exactly, with each increment `e_{b_j}` computed from its definition by integer
comparisons, gives `b_42 = 256`; the first terms are `b_0, …, b_6 = 9, 10, …, 15`.

## Main results

* `CollatzPosDens.scale_42`: `b_42 = 256`.
* `CollatzPosDens.two_hundred_fifty_six_le_scale`: `256 ≤ b_n` for `n ≥ 42`.
* `CollatzPosDens.scale_42_add`: for `k ∈ ℕ`, `b_{42+k}` is the `k`-th iterate of
  `b ↦ b + ⌈b/100⌉` at `256`.

## Implementation notes

Both `scale` and `eb` are computable natural-number functions with decidable branches, so the
value is obtained by kernel evaluation of the recursion on numerals.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §15.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The scale `b_42`**: `b_42 = 256`. -/
@[collatz_pos_dens "lem_scales_b42"]
theorem scale_42 : scale 42 = 256 := by
  decide +kernel

/-- For `n ≥ 42`, `256 ≤ b_n`. -/
theorem two_hundred_fifty_six_le_scale {n : ℕ} (hn : 42 ≤ n) : 256 ≤ scale n :=
  scale_42 ▸ scale_monotone hn

/-- `b_{42+k}` is the `k`-th iterate of `b ↦ b + ⌈b/100⌉` started at `256`: from `b_42 = 256`
on, the increment takes its fallback value `e_b = ⌈b/100⌉`. -/
theorem scale_42_add (k : ℕ) :
    scale (42 + k) = (fun b => b + (b + 99) / 100)^[k] 256 := by
  induction k with
  | zero => simpa using scale_42
  | succ k ih =>
    rw [← Nat.add_assoc, scale_succ, eb_of_le (two_hundred_fifty_six_le_scale (by omega)),
      Function.iterate_succ_apply', ← ih]

end CollatzPosDens
