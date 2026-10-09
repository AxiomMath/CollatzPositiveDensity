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
# An upper bound on `Q_m`

Fix a level `n`, a residue `ξ : CollatzPosDens.ResidueGroup n` and a threshold `ε`. For a real
`A ≥ 0` and a natural number `m`, the weighted supremum `Q_m = CollatzPosDens.chQm n ξ ε A m`
is at most `max(m, 1)^A`.

## Main results

* `CollatzPosDens.chQm_le_pow`: `Q_m ≤ max(m, 1)^A`.

## Implementation notes

The power is the real power `Real.rpow`, matching `CollatzPosDens.chQm`. The threshold `ε`
is arbitrary.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **An upper bound on `Q_m`.** For real `A ≥ 0` and `m ≥ 0`, the weighted supremum `Q_m` is
at most `max(m, 1)^A`. -/
@[collatz_pos_dens "lem_ch_Qm_le_pow"]
theorem chQm_le_pow (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    chQm n ξ ε A m ≤ ((max m 1 : ℕ) : ℝ) ^ A :=
  csSup_le (chQm_set_nonempty n ξ ε A m) fun _ hx => chQm_set_le n ξ ε hA m hx

end CollatzPosDens
