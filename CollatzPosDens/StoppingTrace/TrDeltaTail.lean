/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnP3
public import CollatzPosDens.Renewal.RnP45Large
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrE8Pos

/-!
# The passage surplus at large gaps

For every gap `s ≥ 256` the passage surplus satisfies
`δ_tr(s) ≥ (515/2048) E₈(γ_*) - d_*`.
Indeed `p₄₅(s) ≥ 5/16 - 125/(8s) ≥ 5/16 - 125/2048 = 515/2048`, `p₃(s) ≥ 0`, and both
`E₈(γ_*)` and `E₈(κ_* γ_*)` are positive; inserting these bounds in the definition
`δ_tr(s) = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*` gives the claim.

## Main results

* `CollatzPosDens.trDelta_ge_of_le`: `515/2048 · E₈(γ_*) - d_* ≤ δ_tr(s)` for `256 ≤ s`.

## References

* [Mazur, *Collatz positive density*], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `s ≥ 256`, the passage surplus satisfies
`trDelta s ≥ (515/2048) E8 gammaStar - dStar`. -/
@[collatz_pos_dens "lem_tr_delta_tail"]
theorem trDelta_ge_of_le {s : ℕ} (hs : 256 ≤ s) :
    515 / 2048 * E8 (gammaStar : ℝ) - (dStar : ℝ) ≤ trDelta s := by
  have hp45 := p45_ge_of_le hs
  have hs' : (256 : ℝ) ≤ s := by exact_mod_cast hs
  have h1 : (515 / 2048 : ℝ) ≤ p45 s := by
    have : 125 / (8 * (s : ℝ)) ≤ 125 / 2048 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hE := E8_gammaStar_pos
  have hK : 0 ≤ E8 ((kappaStar * gammaStar : ℚ) : ℝ) := by
    rw [Rat.cast_mul]; exact E8_kappaStar_mul_gammaStar_pos.le
  have h3 := p3_nonneg s
  rw [trDelta]
  nlinarith [mul_le_mul_of_nonneg_left h1 hE.le, mul_nonneg hK h3]

end CollatzPosDens
