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
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa

/-!
# The passage surplus at small positive gaps

The passage surplus `δ_tr(s) = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*` satisfies
`δ_tr(s) ≥ δ_tr(6)` for every integer `1 ≤ s ≤ 255`.

For each `s`, the exit masses `p₄₅(s)` and `p₃(s)` are finite sums of raw-prefix masses
`𝖱(k, t)`, with `𝖱(0, t) = [t = 0]` and `𝖱(k, t) = binom(t - 1, 2k - 1) 2^{-t}` for `k ≥ 1`
(zero when `t ≤ 0`). Writing `N = ⌊(5s + 16)/16⌋ = K + 1`, the inner sum over the length is
`∑_{r=1}^{K+1} 𝖱(r - 1, t) = [t = 0] + 2^{-t} ∑_{k<K} binom(t - 1, 2k + 1)`,
and only `t ∈ [s - 4, s]` occurs. Hence `δ_tr(s)` is an explicit rational, and the `255`
inequalities are checked by exact rational evaluation.

## Main results

* `CollatzPosDens.trDelta_rows`: `δ_tr(6) ≤ δ_tr(s)` for `1 ≤ s ≤ 255`.

## Implementation notes

The odd-index binomial sums `∑_{k<K} binom(m, 2k + 1)` are evaluated by walking along row `m`
of Pascal's triangle with the ratio `binom(m, j + 1) = binom(m, j) (m - j) / (j + 1)`, so each
row costs `O(K)` exact multiplications. The resulting rational inequalities are discharged by
kernel evaluation (`decide +kernel`), after the exact identities `p₄₅(s) = p₄₅^ℚ(s)` and
`p₃(s) = p₃^ℚ(s)` with these rational models are proved for every `s`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §9.4.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The rational inequalities behind `trDelta_rows`, checked by exact evaluation. -/
private theorem rows_check : ∀ s ∈ Icc 1 255,
    trDeltaMassQ 6 ≤ trDeltaMassQ s := by
  decide +kernel

/-- **The passage surplus at small positive gaps.** For every integer `1 ≤ s ≤ 255`,
`δ_tr(s) ≥ δ_tr(6)`. -/
@[collatz_pos_dens "lem_tr_delta_rows"]
theorem trDelta_rows {s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ 255) : trDelta 6 ≤ trDelta s := by
  have key := rows_check s (mem_Icc.mpr ⟨h1, h2⟩)
  have key' := (Rat.cast_le (K := ℝ)).mpr key
  simp only [trDelta, p45_eq_p45Q, p3_eq_p3Q, E8_ratCast, gammaStar_eq, kappaStar_def]
  push_cast at key' ⊢
  simp only [trDeltaMassQ, E8Q] at key'
  push_cast at key'
  linarith

end CollatzPosDens
