/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxLevel

/-!
# The head window

For `k l : ℕ` and a word `h ∈ mxHeadGate n k l`, the valuation sum `l` satisfies
$$l + \tfrac{4609}{4096} \log_2 n < n \log_2 3.$$
Indeed, membership in `mxHeadGate n k l` gives `l ≤ ⌊mxLevel n⌋ + 1 + ⌈(9/8) log₂ n⌉`, which with
`⌊x⌋ ≤ x` and `⌈x⌉ < x + 1` yields `l < mxLevel n + (9/8) log₂ n + 2`; by `mxLevel_def`,
`mxLevel n + 2 = n log₂ 3 - (9217/4096) log₂ n`, while `9/8 = 4608/4096`.

## Main results

* `CollatzPosDens.mxHeadGate_add_logb_lt`: `l + (4609/4096) log₂ n < n log₂ 3` for
  `h ∈ mxHeadGate n k l`.

## Implementation notes

The bound holds for every natural number `n`, including `n = 0`, where `mxLevel 0` takes its junk
value; no hypothesis `1 ≤ n` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The head window: for `h ∈ mxHeadGate n k l`, `l + (4609/4096) log₂ n < n log₂ 3`. -/
@[collatz_pos_dens "lem_mx_head_window"]
theorem mxHeadGate_add_logb_lt {n k l : ℕ} {h : Word} (hh : h ∈ mxHeadGate n k l) :
    (l : ℝ) + 4609 / 4096 * Real.logb 2 n < n * Real.logb 2 3 := by
  obtain ⟨-, -, -, hl, -⟩ := mem_mxHeadGate.mp hh
  have hfl := Int.floor_le (mxLevel n)
  have hce := Int.ceil_lt_add_one ((9 / 8 : ℝ) * Real.logb 2 n)
  have hl' : (l : ℝ) ≤ (⌊mxLevel n⌋ : ℝ) + 1 + (⌈(9 / 8 : ℝ) * Real.logb 2 n⌉ : ℝ) := by
    exact_mod_cast hl
  rw [mxLevel_def] at hfl hl'
  linarith

end CollatzPosDens
