/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaTail
public import CollatzPosDens.StoppingTrace.TrMu
public import CollatzPosDens.StoppingTrace.TrWFar
public import CollatzPosDens.StoppingTrace.TrWMixed
public import CollatzPosDens.StoppingTrace.TrWRows

/-!
# The adjacent surplus at every height

The weighted adjacent combination of passage surpluses
`(3/16) δ_tr(k) + (1/8) δ_tr(k - 1)` is at least the adjacent surplus `μ_∘` for every
integer `k ≥ 1`. The proof splits into three ranges:

* for `1 ≤ k ≤ 255` this is the finite row check `CollatzPosDens.trW_rows`;
* for `k = 256` the tail bound `CollatzPosDens.trDelta_ge_of_le`, giving
  `δ_tr(256) ≥ (515/2048) E₈(γ_*) - d_*`, and the mixed inequality
  `CollatzPosDens.trMu_lt_mixed` conclude;
* for `k ≥ 257` both `k` and `k - 1` are at least `256`, so the tail bound applies to both
  terms, and the combination is at least `(5/16) ((515/2048) E₈(γ_*) - d_*)`, which exceeds
  `μ_∘` by `CollatzPosDens.trMu_lt_far`.

## Main results

* `CollatzPosDens.trMu_le_trW`:
  `μ_∘ ≤ (3/16) δ_tr(k) + (1/8) δ_tr(k - 1)` for every `k ≥ 1`.

## Implementation notes

Heights are natural numbers; since `k ≥ 1`, the truncated subtraction `k - 1` in `ℕ` is the
honest predecessor.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The adjacent surplus at every height.** For every integer `k ≥ 1`,
`(3/16) δ_tr(k) + (1/8) δ_tr(k - 1) ≥ μ_∘`. -/
@[collatz_pos_dens "lem_tr_W"]
theorem trMu_le_trW {k : ℕ} (hk : 1 ≤ k) :
    trMu ≤ 3 / 16 * trDelta k + 1 / 8 * trDelta (k - 1) := by
  rcases le_or_gt k 255 with h | h
  · exact trW_rows hk h
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
  · subst h'
    have := trDelta_ge_of_le (le_refl 256)
    have := trMu_lt_mixed
    simp only [Nat.succ_sub_one]
    linarith
  · have h1 := trDelta_ge_of_le (s := k) (by omega)
    have h2 := trDelta_ge_of_le (s := k - 1) (by omega)
    have := trMu_lt_far
    linarith

end CollatzPosDens
