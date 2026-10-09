/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDelta

/-!
# The adjacent surplus `μ_∘`

The *adjacent surplus* is the constant
`μ_∘ = (3/16) δ_tr(6) + (1/8) δ_tr(5)`,
where `δ_tr = CollatzPosDens.trDelta` is the passage surplus. It is the weighted adjacent
combination `(3/16) δ_tr(k) + (1/8) δ_tr(k - 1)` at `k = 6`.

## Main definitions

* `CollatzPosDens.trMu`: the adjacent surplus `μ_∘ : ℝ`.

## Main results

* `CollatzPosDens.trMu_def`: the defining identity
  `μ_∘ = 3/16 * δ_tr(6) + 1/8 * δ_tr(5)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The adjacent surplus `μ_∘ = (3/16) δ_tr(6) + (1/8) δ_tr(5)`. -/
@[collatz_pos_dens "def_tr_mu"]
noncomputable def trMu : ℝ :=
  3 / 16 * trDelta 6 + 1 / 8 * trDelta 5

/-- The defining identity of the adjacent surplus. -/
theorem trMu_def : trMu = 3 / 16 * trDelta 6 + 1 / 8 * trDelta 5 := rfl

end CollatzPosDens
