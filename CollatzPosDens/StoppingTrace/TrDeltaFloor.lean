/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaRows
public import CollatzPosDens.StoppingTrace.TrDeltaTail
public import CollatzPosDens.StoppingTrace.TrTstar

/-!
# The passage surplus is minimised at gap six

The passage surplus `δ_tr(s) = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*` attains its minimum
over the positive gaps `s ≥ 1` at `s = 6`. For `1 ≤ s ≤ 255` this is the exact row-by-row
comparison; for `s ≥ 256` the surplus is at least the large-gap floor
`(515/2048) E₈(γ_*) - d_*`, which strictly exceeds `δ_tr(6)`.

## Main results

* `CollatzPosDens.trDelta_six_le`: `δ_tr(6) ≤ δ_tr(s)` for every `s ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The passage surplus is minimised at gap six: for every integer `s ≥ 1`,
`δ_tr(s) ≥ δ_tr(6)`. -/
@[collatz_pos_dens "lem_tr_delta_floor"]
theorem trDelta_six_le {s : ℕ} (hs : 1 ≤ s) : trDelta 6 ≤ trDelta s := by
  rcases le_or_gt s 255 with h | h
  · exact trDelta_rows hs h
  · exact (trDelta_six_lt_floor.trans_le (trDelta_ge_of_le h)).le

end CollatzPosDens
