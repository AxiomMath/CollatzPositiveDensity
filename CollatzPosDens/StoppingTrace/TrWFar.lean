/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.StoppingTrace.TrMu
public import CollatzPosDens.StoppingTrace.TrMuValue
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma

/-!
# The adjacent surplus at large heights

At large heights both passage surpluses in the weighted adjacent combination
`(3/16) δ_tr(k) + (1/8) δ_tr(k - 1)` are bounded below by the large-gap floor
`(515/2048) E₈(γ_*) - d_*`, so the combination is at least
`(5/16) ((515/2048) E₈(γ_*) - d_*)`. This quantity strictly exceeds the adjacent surplus
`μ_∘`.

Exact evaluation at `γ_* = 87/200` gives
`(515/2048) E₈(γ_*) - d_*`
`= 20623674158457189646056701180070933 / 3584000000000000000000000000000000000`,
and with the exact value of `μ_∘` the difference is
`7931160207410188961115429252376059 / 57344000000000000000000000000000000000 > 0`.

## Main results

* `CollatzPosDens.trMu_lt_far`:
  `μ_∘ < (5/16) ((515/2048) E₈(γ_*) - d_*)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The adjacent surplus at large heights.**
`(5/16) ((515/2048) E₈(γ_*) - d_*) > μ_∘`. -/
@[collatz_pos_dens "lem_tr_W_far"]
theorem trMu_lt_far :
    trMu < 5 / 16 * (515 / 2048 * E8 (gammaStar : ℝ) - (dStar : ℝ)) := by
  rw [trMu_value, E8_ratCast, dStar_eq, gammaStar_eq]
  push_cast
  norm_num

end CollatzPosDens
