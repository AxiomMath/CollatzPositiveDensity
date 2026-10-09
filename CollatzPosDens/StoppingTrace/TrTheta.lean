/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrMu

/-!
# The white-bridge floor `θ_∘`

The *white-bridge floor* is the constant `θ_∘ = (10000/3299) μ_∘`, a fixed rational multiple of
the adjacent surplus `μ_∘ = CollatzPosDens.trMu = (3/16) trDelta 6 + (1/8) trDelta 5`.

## Main definitions

* `CollatzPosDens.trTheta`: the white-bridge floor `θ_∘ : ℝ`.

## Main results

* `CollatzPosDens.trTheta_def`: the defining identity `θ_∘ = 10000/3299 * μ_∘`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The white-bridge floor `θ_∘ = (10000/3299) μ_∘`. -/
@[collatz_pos_dens "def_tr_theta"]
noncomputable def trTheta : ℝ :=
  10000 / 3299 * trMu

/-- The defining identity of the white-bridge floor. -/
theorem trTheta_def : trTheta = 10000 / 3299 * trMu := rfl

end CollatzPosDens
