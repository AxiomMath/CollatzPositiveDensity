/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChQmNonempty
public import CollatzPosDens.CharSum.ChQmSetBound

/-!
# Monotonicity of `Q_m` in `m`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a real `A ≥ 0` and integers
`0 ≤ a ≤ b`, the weighted suprema satisfy `Q_a ≤ Q_b`. Indeed `⌊n/2⌋ ∸ b ≤ ⌊n/2⌋ ∸ a`, so the
set defining `Q_a` is contained in the set defining `Q_b`; the former is nonempty and the latter
is bounded above by `max(b, 1)^A`, so the suprema compare.

## Main results

* `CollatzPosDens.chQm_mono`: `m ↦ Q_m` is monotone, i.e. `Q_a ≤ Q_b` for `a ≤ b`.

## Implementation notes

The statement is phrased as `Monotone (chQm n ξ ε A)`, which unfolds to `Q_a ≤ Q_b` for all
`a ≤ b`. The threshold `ε` is arbitrary.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- For real `A ≥ 0`, `Q_m` is monotone in `m`: for `a ≤ b`, `Q_a ≤ Q_b`. -/
@[collatz_pos_dens "lem_ch_Qm_mono"]
theorem chQm_mono (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    Monotone (chQm n ξ ε A) := by
  intro a b hab
  refine csSup_le_csSup (chQm_set_bddAbove n ξ ε hA b) (chQm_set_nonempty n ξ ε A a) ?_
  rintro x ⟨p, hp, hj, rfl⟩
  exact ⟨p, hp, le_trans (by omega) hj, rfl⟩

end CollatzPosDens
