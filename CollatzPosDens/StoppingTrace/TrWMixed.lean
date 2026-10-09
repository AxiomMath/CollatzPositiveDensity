/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnP3
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaRat
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.StoppingTrace.TrMu
public import CollatzPosDens.StoppingTrace.TrMuValue
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa

/-!
# The adjacent surplus at the mixed height

The weighted adjacent combination at height `k = 256` mixes the tail bound
`δ_tr(256) ≥ (515/2048) E₈(γ_*) - d_*` with the exact passage surplus at gap `255`, and it exceeds
the adjacent surplus: `(3/16) ((515/2048) E₈(γ_*) - d_*) + (1/8) δ_tr(255) > μ_∘`.

Exact rational evaluation gives `(3/16) ((515/2048) E₈(γ_*) - d_*) ≥ 10789/10⁷`. At gap `255`
the exit masses `p₄₅(255)` and `p₃(255)` are finite sums of raw-prefix masses
`𝖱(k, t) = binom(t - 1, 2k - 1) 2^{-t}` (`k ≥ 1`) and `𝖱(0, t) = [t = 0]`, with
`⌊(5 · 255 + 16)/16⌋ = 80`; hence `δ_tr(255)` is an explicit rational, and
`δ_tr(255) ≥ 39886/10⁶`. Since `μ_∘ < 16600/10⁷`, the claim follows.

## Main results

* `CollatzPosDens.le_trDelta_255`: `δ_tr(255) ≥ 39886/10⁶`.
* `CollatzPosDens.trMu_lt_mixed`: the mixed adjacent inequality.

## Implementation notes

For `N = K + 1`, the length-summed raw mass is
`∑_{r=1}^{K+1} 𝖱(r - 1, t) = [t = 0] + 2^{-t} ∑_{k<K} binom(t - 1, 2k + 1)`. The odd-index
binomial sums are evaluated by walking along row `t - 1` of Pascal's triangle with the ratio
`binom(m, j + 1) = binom(m, j) (m - j) / (j + 1)`. This gives rational models of `p₄₅(s)` and
`p₃(s)`, proved equal to them for every `s`; the single rational inequality at `s = 255` is then
discharged by kernel evaluation (`decide +kernel`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The rational inequality behind `le_trDelta_255`, checked by exact evaluation. -/
private theorem trDeltaMassQ_255_check :
    39886 / 10 ^ 6 + 331784646551677809785190276273027 / 4000000000000000000000000000000000 ≤
      trDeltaMassQ 255 := by
  decide +kernel

/-- The passage surplus at gap `255`: `δ_tr(255) ≥ 39886/10⁶`. -/
theorem le_trDelta_255 : (39886 / 10 ^ 6 : ℝ) ≤ trDelta 255 := by
  have key' := (Rat.cast_le (K := ℝ)).mpr trDeltaMassQ_255_check
  simp only [trDelta, p45_eq_p45Q, p3_eq_p3Q, E8_ratCast, gammaStar_eq, kappaStar_def,
    dStar_eq]
  push_cast at key' ⊢
  simp only [trDeltaMassQ, E8Q] at key'
  push_cast at key'
  linarith

/-- **The adjacent surplus at the mixed height.**
`(3/16) ((515/2048) E₈(γ_*) - d_*) + (1/8) δ_tr(255) > μ_∘`. -/
@[collatz_pos_dens "lem_tr_W_mixed"]
theorem trMu_lt_mixed :
    trMu < 3 / 16 * (515 / 2048 * E8 (gammaStar : ℝ) - (dStar : ℝ)) + 1 / 8 * trDelta 255 := by
  have h := le_trDelta_255
  rw [trMu_value, E8_ratCast, gammaStar_eq, dStar_eq]
  push_cast
  norm_num
  linarith

end CollatzPosDens
