/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxWindowHighBound

/-!
# The index of a nonempty head gate is bounded

Let `n ≥ 2^131072` and `k, l ∈ ℕ`. If the head gate `mxHeadGate n k l` is nonempty, then
`20 k ≤ 17 n`. Indeed, the window condition of the head gate gives `k + 1 ≤ mxWindowHigh n`, and
`mxWindowHigh n < (13/16) n` by `mxWindowHigh_bound`; hence `20 k < (65/4) n ≤ 17 n`.

## Main results

* `CollatzPosDens.mxHeadGate_index_le`: if `n ≥ 2^131072` and `mxHeadGate n k l ≠ ∅` then
  `20 k ≤ 17 n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `n ≥ 2^131072` and the head gate `mxHeadGate n k l` is nonempty, then `20 k ≤ 17 n`. -/
@[collatz_pos_dens "lem_mx_head_index"]
theorem mxHeadGate_index_le {n k l : ℕ} (hn : 2 ^ 131072 ≤ n)
    (hne : mxHeadGate n k l ≠ ∅) : 20 * k ≤ 17 * n := by
  obtain ⟨h, -, ⟨-, hk⟩, -⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hq := mxWindowHigh_bound n hn
  have : (20 : ℤ) * k ≤ 17 * n := by omega
  exact_mod_cast this

end CollatzPosDens
