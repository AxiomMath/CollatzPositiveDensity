/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQfiniteRange

/-!
# The range of the renewal function `Q`

Fix a level `n`, a residue `ξ : ResidueGroup n` and a threshold `ε`. For every point `p`, the
renewal function satisfies `0 ≤ Q(p) ≤ 1`. Since `Q(p)` is by definition the finite-horizon
white product `Q^{(J)}(p)` at the horizon `J = ⌊n/2⌋`, this is the range bound for the
finite-horizon white products at that horizon.

## Main results

* `CollatzPosDens.chQ_le_one`: `Q(p) ≤ 1`.
* `CollatzPosDens.chQ_mem_Icc`: `Q(p) ∈ [0, 1]`.
* `CollatzPosDens.chQ_range`: `0 ≤ Q(p) ∧ Q(p) ≤ 1`.

## Implementation notes

The base point `p` ranges over all of `ℤ × ℤ` and the threshold `ε` is arbitrary.
-/

@[expose] public section

namespace CollatzPosDens

/-- The renewal function is at most `1`: `Q(p) ≤ 1`. -/
theorem chQ_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    chQ n ξ ε p ≤ 1 :=
  chQFinite_le_one n ξ ε (n / 2) p

/-- The renewal function lies in `[0, 1]`. -/
theorem chQ_mem_Icc (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    chQ n ξ ε p ∈ Set.Icc (0 : ℝ) 1 :=
  chQFinite_mem_Icc n ξ ε (n / 2) p

/-- **Range of `Q`.** For every point `p`, `0 ≤ Q(p) ≤ 1`. -/
@[collatz_pos_dens "lem_ch_Q_range"]
theorem chQ_range (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    0 ≤ chQ n ξ ε p ∧ chQ n ξ ε p ≤ 1 :=
  ⟨chQ_nonneg n ξ ε p, chQ_le_one n ξ ε p⟩

end CollatzPosDens
