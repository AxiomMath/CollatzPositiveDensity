/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrConcat
public import CollatzPosDens.StoppingTrace.TrConcatShift

/-!
# The weighted white count of a concatenation

Fix a level `n` and a residue `ξ ∈ G_n`. For a base point `o ∈ 𝒫` and block lists `u ∈ 𝔅^a`,
`f ∈ 𝔅^b`, the weighted white count of the concatenation `uf` splits at time `a`:
```
N^*(o, uf; a + t) = N^*(o, u; a) + N^*(x_a(o, u), f; t)
```
for every `t ∈ ℕ`. Indeed the first `a` blocks of `uf` are those of `u`, read along the path of
`u`, while its block `a + i` is the block `i` of `f`, read along the path of `f` started at the
endpoint `x_a(o, u)`.

## Main results

* `CollatzPosDens.trCount_concat`:
  `N^*(o, uf; a + t) = N^*(o, u; a) + N^*(x_a(o, u), f; t)` for `|u| = a`.

## Implementation notes

The identity holds for every base point `o ∈ ℤ × ℤ` and every pair of lists of `List ℤ × ℤ`,
with no condition on the closing letters, so the hypotheses `o ∈ 𝒫`, `u ∈ 𝔅^a` and `f ∈ 𝔅^b`
are not needed; the length `a` of `u` is recorded as `u.length = a`, and the length `b` of `f`
plays no role.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The weighted white count is additive under concatenation:
`N^*(o, uf; a + t) = N^*(o, u; a) + N^*(x_a(o, u), f; t)` for `|u| = a`. -/
@[collatz_pos_dens "lem_tr_count_concat"]
theorem trCount_concat {n : ℕ} (ξ : ResidueGroup n) (o : ℤ × ℤ) (u f : List (List ℤ × ℤ))
    {a : ℕ} (hu : u.length = a) (t : ℕ) :
    trCount n ξ o (u ++ f) (a + t) =
      trCount n ξ o u a + trCount n ξ (trPath o u a) f t := by
  rw [trCount_def, trCount_def, trCount_def, List.length_append, hu, Nat.add_min_add_left,
    min_self, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi : i < u.length := hu ▸ Finset.mem_range.1 hi
    rw [trPath_concat o u f hi.le, List.getD_append _ _ _ _ hi]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [trPath_append_add o u f hu, ← hu, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]

end CollatzPosDens
