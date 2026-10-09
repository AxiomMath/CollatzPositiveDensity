/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrBetaPos
public import CollatzPosDens.StoppingTrace.TrDeltaFloor
public import CollatzPosDens.StoppingTrace.TrDeltaZero

/-!
# Nonnegativity of the passage surplus

The passage surplus `trDelta s = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*` is nonnegative at
every gap `s ∈ ℕ`. At `s = 0` it vanishes; for `s ≥ 1` it is at least `trDelta 6`, which is
strictly positive.

## Main results

* `CollatzPosDens.trDelta_nonneg`: `0 ≤ trDelta s` for every `s ∈ ℕ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The passage surplus is nonnegative: `0 ≤ trDelta s` for every `s ∈ ℕ`. -/
@[collatz_pos_dens "lem_tr_delta_nonneg"]
theorem trDelta_nonneg (s : ℕ) : 0 ≤ trDelta s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact trDelta_zero.ge
  · exact trDelta_six_pos.le.trans (trDelta_six_le hs)

end CollatzPosDens
