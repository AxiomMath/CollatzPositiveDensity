/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaSix

/-!
# Positivity of the passage surplus at gap six

The passage surplus `trDelta s = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*` is strictly
positive at `s = 6`: by `trDelta_six`, its exact value is a quotient of two positive integers.

## Main results

* `CollatzPosDens.trDelta_six_pos`: `0 < trDelta 6`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The passage surplus at gap six is strictly positive: `0 < trDelta 6`. -/
@[collatz_pos_dens "lem_tr_beta_pos"]
theorem trDelta_six_pos : 0 < trDelta 6 := by
  rw [trDelta_six]
  norm_num

end CollatzPosDens
