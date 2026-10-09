/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaSix
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma

/-!
# The large-gap floor exceeds the small-gap minimum

With the trace tilt `γ_* = 87/200`, the eighth-order exponential defect `E₈` and the
single-passage loss `d_*`, the large-gap floor `(515/2048) E₈(γ_*) - d_*` strictly exceeds the
passage surplus at gap six, `δ_tr(6)`. Exact evaluation gives
`(515/2048) E₈(γ_*) - d_*`
`= 20623674158457189646056701180070933 / 3584000000000000000000000000000000000`,
and the difference with `δ_tr(6)` is
`564915793783964412294085399755747 / 143360000000000000000000000000000000 > 0`.

## Main results

* `CollatzPosDens.trDelta_six_lt_floor`: `δ_tr(6) < (515/2048) E₈(γ_*) - d_*`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The large-gap floor exceeds the small-gap minimum:
`δ_tr(6) < (515/2048) E₈(γ_*) - d_*`. -/
@[collatz_pos_dens "lem_tr_tstar"]
theorem trDelta_six_lt_floor :
    trDelta 6 < 515 / 2048 * E8 (gammaStar : ℝ) - (dStar : ℝ) := by
  rw [trDelta_six, E8_ratCast, dStar_eq, gammaStar_eq]
  push_cast
  norm_num

end CollatzPosDens
